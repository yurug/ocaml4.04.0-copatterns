(* Benchmarks. *)

let bench f = Unix.(
    let start = Unix.gettimeofday () in
    let y = f () in
    let stop = Unix.gettimeofday () in
    (y, stop -. start)
  )

(** The cotype stream with two observations : Head and Tail. *)

type 'a !stream = {
  Head : 'a;
  Tail : 'a !stream;
}

let rec ( ** ) f n =
  if n = 0 then fun x -> x
  else fun x -> (f ** (pred n)) (f x)

let nth n s = ((tail ** n) s)#Head

(** Fibonacci examples. *)

(** - Without memoization. *)

let rec map2
  : type a b c. (a -> b -> c) -> a !stream -> b !stream -> c !stream
  = fun f s1 s2 -> cofunction : c !stream with
    | ..#Head -> f s1#Head s2#Head
    | ..#Tail -> map2 f s1#Tail s2#Tail

let corec fib : int !stream with
  | ..#Head -> 1
  | ..#Tail : int !stream with
  | ...#Head -> 1
  | ...#Tail -> map2 ( + ) fib fib#Tail

(** -- With memoization. *)

let rec lazy_map2
  : type a b c. (a -> b -> c) -> a !stream -> b !stream -> c !stream
  = fun f s1 s2 ->
    lazy cofunction : c !stream with
    | ..#Head -> f s1#Head s2#Head
    | ..#Tail -> lazy_map2 f s1#Tail s2#Tail

let rec lazy_fib : int !stream = lazy cofunction : int!stream with
  | ..#Head -> 1
  | ..#Tail : int !stream with
  | ...#Head -> 1
  | ...#Tail -> lazy_map2 ( + ) lazy_fib lazy_fib#Tail

let show_fib is_lazy n =
  let f = if is_lazy then lazy_fib else fib in
  let name = if is_lazy then "lazy fib" else "fib" in
  let (r,t) = bench (fun () -> nth n f) in
  Printf.printf "%s (%d) = %d [in %f seconds]\n" name n r t

(** Simple example of nested copattern matching. *)

type _ repr =
  | Int   : int   -> int repr
  | Bool  : bool  -> bool repr

type _ !qrepr = {
  QInt   : int   <- int !qrepr;
  QBool  : bool  <- bool !qrepr;
}

let corec f : type a. a repr -> a !qrepr with
   | (.. (Int n))#QInt -> n
   | (.. (Bool b))#QBool -> b

(** An indexed codatatype for fair bistream. *)

type read and unread

(** The cotype fairbistream with three observations : Left, Right and BTail. *)

type (_,_) !fairbistream = {
  Left  : int * (read, 'b) !fairbistream <- (unread, 'b) !fairbistream;
  Right : int * ('a, read) !fairbistream <- ('a, unread) !fairbistream;
  BTail : (unread, unread) !fairbistream <- (read, read) !fairbistream;
}

type ('a, 'b, 'e) twobuffer =
| E : ( read, read, 'e ) twobuffer
| L : 'e -> ( unread, read, 'e ) twobuffer
| R : 'e -> ( read, unread, 'e ) twobuffer
| F : 'e * 'e -> ( unread, unread, 'e ) twobuffer

let corec zfrom : type a b. int -> (a,b,int) twobuffer -> (a,b) !fairbistream with
  | (.. n E)#BTail -> zfrom (n + 1) (F (n, -n))
  | (.. n (L x))#Left  -> (x, zfrom n E)
  | (.. n (F (x,y)))#Left  -> (x, zfrom n (R y))
  | (.. n (R x))#Right -> (x, zfrom n E)
  | (.. n (F (x, y)))#Right -> (y, zfrom n (L x))

let z = zfrom 0 (L 0)
let rec stream_of_fairbistream : (unread, unread) !fairbistream -> int !stream
  = fun bi ->
    let corec read_left : (unread, unread) !fairbistream -> int !stream with
      | (.. bi)#Head -> fst bi#Left
      | (.. bi)#Tail -> read_right (snd bi#Left)
    and corec read_right : (read, unread) !fairbistream -> int !stream with
      | (.. bi)#Head -> fst bi#Right
      | (.. bi)#Tail -> stream_of_fairbistream (snd (bi#Right))#BTail
    in read_left bi

let mfive = nth 11 (stream_of_fairbistream (snd z#Left)#BTail)

(** Game of life and zippers. *)

(** The cotype zipper with three observations : Left, Proj, Right. *)

type 'a !zipper = {
  Left  : 'a !stream;
  Proj  : 'a;
  Right : 'a !stream;
}

module type GOL = sig
  val move_left : 'a !zipper -> 'a !zipper
  val move_right : 'a !zipper -> 'a !zipper
  val game_of_life : (bool !zipper) !stream
end

(* Version 1 *)

module GOL_1 = struct

  let corec repeat : type a. a -> a !stream with
    | (..x) #Head -> x
    | (..x) #Tail -> repeat x

  let point : type a. a -> a -> a !zipper
    = fun x y -> cofunction : a !zipper with
    | ..#Left  -> repeat y
    | ..#Proj  -> x
    | ..#Right -> repeat y

  let move_left : type a. a !zipper -> a !zipper =
    fun z -> cofunction : a !zipper with
     | ..#Left -> z#Left#Tail
     | ..#Proj -> z#Left#Head
     | ..#Right : a !stream with
       | ...#Head -> z#Proj
       | ...#Tail -> z#Right

  let move_right : type a. a !zipper -> a !zipper =
    fun z -> cofunction : a !zipper with
     | ..#Left : a !stream with begin
       | ...#Head -> z#Proj
       | ...#Tail -> z#Left
     end
     | ..#Proj  -> z#Right#Head
     | ..#Right -> z#Right#Tail

  let rec map_iterate : type a b. (a -> b) -> (a -> a) -> a -> b !stream
    = fun f shift x -> cofunction : b !stream with
    | ..#Head -> f x
    | ..#Tail -> map_iterate f shift (shift x)

  let cobind : type a b. (a !zipper -> b) -> a !zipper -> b !zipper
    = fun f z -> cofunction : b !zipper with
    | ..#Left  -> map_iterate f move_left (move_left z)
    | ..#Proj  -> f z
    | ..#Right -> map_iterate f move_right (move_right z)

  let rule z =
    let left  = proj (move_left z)
    and middle = proj z
    and right = proj (move_right z) in
    not (left && middle && not right || left = middle)

  let rec iterate : type a. (a -> a) -> a -> a !stream
    = fun f a -> cofunction : a !stream with
    | ..#Head -> a
    | ..#Tail -> iterate f (f a)

  let game_of_life = iterate (cobind rule) (point true false)

end

(* Version 2 with memoization. *)

module GOL_2 = struct

  let corec lazy repeat : type a. a -> a !stream with
    | (..x) #Head -> x
    | (..x) #Tail -> repeat x

  let point : type a. a -> a -> a !zipper
    = fun x y -> lazy cofunction : a !zipper with
    | ..#Left  -> repeat y
    | ..#Proj  -> x
    | ..#Right -> repeat y

  let move_left : type a. a !zipper -> a !zipper =
    fun z -> lazy cofunction : a !zipper with
     | ..#Left -> z#Left#Tail
     | ..#Proj -> z#Left#Head
     | ..#Right : a !stream with
       | ...#Head -> z#Proj
       | ...#Tail -> z#Right

  let move_right : type a. a !zipper -> a !zipper =
    fun z -> lazy cofunction : a !zipper with
     | ..#Left : a !stream with begin
       | ...#Head -> z#Proj
       | ...#Tail -> z#Left
     end
     | ..#Proj  -> z#Right#Head
     | ..#Right -> z#Right#Tail

  let rec map_iterate : type a b. (a -> b) -> (a -> a) -> a -> b !stream
    = fun f shift x -> lazy cofunction : b !stream with
    | ..#Head -> f x
    | ..#Tail -> map_iterate f shift (shift x)

  let cobind : type a b. (a !zipper -> b) -> a !zipper -> b !zipper
    = fun f z -> lazy cofunction : b !zipper with
    | ..#Left  -> map_iterate f move_left (move_left z)
    | ..#Proj  -> f z
    | ..#Right -> map_iterate f move_right (move_right z)

  let rule z =
    let left  = proj (move_left z)
    and middle = proj z
    and right = proj (move_right z) in
    not (left && middle && not right || left = middle)

  let rec iterate : type a. (a -> a) -> a -> a !stream
    = fun f a -> lazy cofunction : a !stream with
    | ..#Head -> a
    | ..#Tail -> iterate f (f a)

  let game_of_life = iterate (cobind rule) (point true false)

end

(* Version 3 with memoization and using reified observation.  *)

module GOL_3 = struct

  let corec lazy repeat : type a. a -> a !stream with
    | (..x) #Head -> x
    | (..x) #Tail -> repeat x

  let point : type a. a -> a -> a !zipper
    = fun x y -> lazy cofunction : a !zipper with
    | ..#Left  -> repeat y
    | ..#Proj  -> x
    | ..#Right -> repeat y

  let custom_dispatch : type a.
    ((a query, a) zipper -> a) ->
    (((a !stream) query, a) zipper -> a !stream) ->
    a !zipper
    = fun pr dir -> cofunction : a !zipper with
      | ..#Proj -> pr Proj
      | ..#Left -> dir Left
      | ..#Right -> dir Right

  let move : type a.
    ((a !stream) query, a) zipper ->
    (a !zipper -> a !stream) ->
    (a !zipper -> a !stream) ->
    a !zipper -> a !zipper
    = fun dir fwd bwd z ->
       let corec bs : a !stream with
         | ..#Head -> z#Proj
         | ..#Tail -> bwd z
       in
       custom_dispatch
         (fun _ -> (fwd z)#Head)
         (fun dir' -> if dir = dir' then (fwd z)#Tail else bs)

  let move_left z = move Left left right z
  let move_right z = move Right right left z

  let rec map_iterate : type a b. (a -> b) -> (a -> a) -> a -> b !stream
    = fun f shift x -> lazy cofunction : b !stream with
    | ..#Head -> f x
    | ..#Tail -> map_iterate f shift (shift x)

  let cobind : type a b. (a !zipper -> b) -> a !zipper -> b !zipper
    = fun f z -> lazy cofunction : b !zipper with
    | ..#Left  -> map_iterate f move_left (move_left z)
    | ..#Proj  -> f z
    | ..#Right -> map_iterate f move_right (move_right z)

  let rule z =
    let left  = proj (move_left z)
    and middle = proj z
    and right = proj (move_right z) in
    not (left && middle && not right || left = middle)

  let rec iterate : type a. (a -> a) -> a -> a !stream
    = fun f a -> lazy cofunction : a !stream with
    | ..#Head -> a
    | ..#Tail -> iterate f (f a)

  let game_of_life = iterate (cobind rule) (point true false)

end

let print (module G : GOL) z =
  let r = ref z in
  for i = 1 to 2 do r := G.move_left !r done;
  for i = 1 to 10 do
    print_char (if proj !r then '#' else '.');
    r := G.move_right !r
  done;
  print_newline ()

let show_gol n =
  let (module G : GOL) = match n with
    | 1 -> (module GOL_1)
    | 2 -> (module GOL_2)
    | 3 -> (module GOL_3)
    | _ -> assert false
  in
  let name = Printf.sprintf "Game of life version %d" n in
  let ((),t) = bench (fun () ->
      for i = 1 to 12 do
        print (module G) (nth i G.game_of_life)
      done)
  in
  Printf.printf "%s [in %f seconds]\n" name t

(* Benchs. *)

let () =
  show_fib false 10;
  show_fib true 10;
  show_fib false 30;
  show_fib true 30;
  show_gol 1;
  show_gol 2;
  show_gol 3
