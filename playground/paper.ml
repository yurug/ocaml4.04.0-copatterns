(** A codatatype for stream. *)
type 'a !stream = {
    Head : 'a;
    Tail : 'a !stream
}

let rec map2
  : type a b c. (a -> b -> c) -> a !stream -> b !stream -> c !stream
  = fun f s1 s2 ->
    comatch r : c !stream with
    | r#Head -> f s1#Head s2#Head
    | r#Tail -> map2 f s1#Tail s2#Tail

let fib : int !stream = comatch fib : int !stream with
  | fib#Head -> 1
  | fib#Tail : int !stream with
  | ..#Head -> 1
  | ..#Tail -> map2 ( + ) fib fib#Tail

let rec ( ** ) f n =
  if n = 0 then fun x -> x
  else fun x -> (f ** (n - 1)) (f x)

let nth n s = ((tail ** n) s)#Head

let rec lazy_map2
  : type a b c. (a -> b -> c) -> a !stream -> b !stream -> c !stream
  = fun f s1 s2 ->
    lazy comatch r : c !stream with
    | r#Head -> f s1#Head s2#Head
    | r#Tail -> lazy_map2 f s1#Tail s2#Tail

let lazy_fib : int !stream = lazy comatch fib : int !stream with
  | fib#Head -> 1
  | fib#Tail : int !stream with
  | ..#Head -> 1
  | ..#Tail -> lazy_map2 ( + ) fib fib#Tail

let bench f =
Unix.(
    let start = Unix.gettimeofday () in
    let y = f () in
    let stop = Unix.gettimeofday () in
    (y, stop -. start)
)

let f5 = nth 5 fib
let f30, et_f30 = bench (fun () -> nth 30 fib)
let fast_f30, et_fast_f30 = bench (fun () -> nth 30 lazy_fib)

(** An indexed codatatype for fair bistream. *)
type read = Read
type unread = Unread

type (_,_) !fairbistream = {
  Left  : int * (read , 'b) !fairbistream <- (unread, 'b) !fairbistream;
  Right : int * ('a , read) !fairbistream <- ('a, unread) !fairbistream;
  BTail : (unread , unread) !fairbistream <- (read, read) !fairbistream;
}

type ( 'a , 'b , 'e ) twobuffer =
| E : ( read , read , 'e ) twobuffer
| L : 'e -> ( unread , read , 'e ) twobuffer
| R : 'e -> ( read , unread , 'e ) twobuffer
| F : 'e * 'e -> ( unread , unread , 'e ) twobuffer

(* fixme *)
let z : (unread, read) ! fairbistream =
  let rec zfrom' : type a b . int -> (a , b , int ) twobuffer -> (a , b ) ! fairbistream = fun n buf ->
    comatch zf : (a,b) ! fairbistream with
    | zf#BTail -> (match buf with E -> zfrom' (n + 1) (F (n, -n)))
    | zf#Left  -> (match buf with L x -> (x, zfrom' n E) | F (x, y) -> (x, zfrom' n (R y)))
    | zf#Right -> (match buf with R x -> (x, zfrom' n E) | F (x, y) -> (y, zfrom' n (L x)))
  in zfrom' 0 (L 0)

(* fixme *)
let rec stream_of_fairbistream : (unread, unread) !fairbistream -> int !stream = fun bi ->
  let rec read_left : (unread, unread) !fairbistream -> int !stream = fun bi ->
   comatch s : int !stream with
   | s#Head -> fst (left bi)
   | s#Tail -> (read_right (snd (left bi)) : int !stream)
  and read_right : (read, unread) !fairbistream -> int !stream = fun bi ->
   comatch s : int !stream with
   | s#Head -> fst (right bi)
   | s#Tail -> stream_of_fairbistream (bTail (snd (right bi)))
  in
  read_left bi

let mfive = nth 11 (stream_of_fairbistream (snd z#Left)#BTail)

let show = Printf.printf "
fib 5       = %d
fib 30      = %d [in %f seconds]
fast fib 30 = %d [in %f seconds]
minus five  = %d
\n%!" f5 f30 et_f30 fast_f30 et_fast_f30 mfive

type 'a !comonad = {
  Left  : 'a !stream;
  Proj  : 'a;
  Right : 'a !stream;
}

module GameOfLifeV1 = struct

let repeat : type a. a -> a !stream = fun x -> comatch s : a !stream with
| s#Head -> x
| s#Tail -> s

let point : type a. a -> a -> a !comonad = fun x y -> comatch c : a !comonad with
| c#Left  -> repeat y
| c#Proj  -> x
| c#Right -> repeat y

let go_left : type a. a !comonad -> a !comonad =
  fun com -> comatch c : a !comonad with
   | c#Left -> com#Left#Tail
   | c#Proj -> com#Left#Head
   | c#Right : a !stream with
     | ..#Head -> com#Proj
     | ..#Tail -> com#Right

let go_right : type a. a !comonad -> a !comonad =
  fun com -> comatch c : a !comonad with
   | c#Left : a !stream with begin
     | ..#Head -> proj com
     | ..#Tail -> left com
   end
   | c#Proj -> com#Right#Head
   | c#Right -> com#Right#Tail

let rec map_iterate : type a b. (a -> b) -> (a -> a) -> a -> b !stream =
  fun f shift c -> comatch s : b !stream with
    | s#Head -> f c
    | s#Tail -> map_iterate f shift (shift c)

let cobind : type a b. (a !comonad -> b) -> a !comonad -> b !comonad =
  fun f c -> comatch com : b !comonad with
   | com#Left -> map_iterate f go_left (go_left c)
   | com#Proj -> f c
   | com#Right -> map_iterate f go_right (go_right c)

let rule (c: bool !comonad) =
  let left  = proj (go_left c)
  and middle = proj c
  and right = proj (go_right c) in
  not (left && middle && not right || (left = middle))

let rec fold
  : type a. (a -> a) -> a -> a !stream
  = fun f a -> comatch r : a !stream with
    | r#Head -> a
    | r#Tail -> fold f (f a)

let game_of_life = fold (cobind rule) (point true false)

let print c =
  let r = ref c in
  for i = 1 to 20 do r := go_left !r done;
  for i = 1 to 40 do
    print_char (if proj !r then '#' else '.');
    r := go_right !r
  done;
  print_newline ()

let show, et_show = bench (fun () ->
  for i = 1 to 10 do
    print (nth i game_of_life)
  done)

let _ = Printf.printf "In %f seconds.\n" et_show

end

module GameOfLifeV2 = struct

let repeat : type a. a -> a !stream = fun x ->
  lazy comatch s : a !stream with
  | s#Head -> x
  | s#Tail -> s

let point : type a. a -> a -> a !comonad = fun x y ->
  lazy comatch c : a !comonad with
  | c#Left  -> repeat y
  | c#Proj  -> x
  | c#Right -> repeat y

let go_left : type a. a !comonad -> a !comonad =
  fun com -> lazy comatch c : a !comonad with
   | c#Left -> com#Left#Tail
   | c#Proj -> com#Left#Head
   | c#Right : a !stream with
     | ..#Head-> com#Proj
     | ..#Tail -> com#Right

let go_right : type a. a !comonad -> a !comonad =
  fun com -> lazy comatch c : a !comonad with
   | c#Left : a !stream with begin
   | ..#Head -> com#Proj
   | ..#Tail -> com#Left
   end
   | c#Proj -> com#Right#Head
   | c#Right -> com#Right#Tail

let rec map_iterate : type a b. (a -> b) -> (a -> a) -> a -> b !stream
  = fun f shift c -> lazy comatch s : b !stream with
| s#Head -> f c
| s#Tail -> map_iterate f shift (shift c)

let cobind : type a b. (a !comonad -> b) -> a !comonad -> b !comonad =
  fun f c -> lazy comatch com : b !comonad with
| com#Left -> map_iterate f go_left (go_left c)
| com#Proj -> f c
| com#Right -> map_iterate f go_right (go_right c)

let rule (c: bool !comonad) =
  let left  = proj (go_left c)
  and middle = proj c
  and right = proj (go_right c) in
  not (left && middle && not right || (left = middle))

let rec fold
  : type a. (a -> a) -> a -> a !stream
  = fun f a -> comatch r : a !stream with
     | r#Head -> a
     | r#Tail -> fold f (f a)

let game_of_life = fold (cobind rule) (point true false)

let print c =
  let r = ref c in
  for i = 1 to 20 do r := go_left !r done;
  for i = 1 to 40 do
    print_char (if proj !r then '#' else '.');
    r := go_right !r
  done;
  print_newline ()

let show, et_show = bench (fun () ->
  for i = 1 to 10 do
    print (nth i game_of_life)
  done)

let _ = Printf.printf "In %f seconds.\n" et_show

end

module GameOfLifeV3 = struct

let repeat : type a. a -> a !stream = fun x ->
  lazy comatch s : a !stream with
  | s#Head -> x
  | s#Tail -> s

let point : type a. a -> a -> a !comonad =
  fun x y -> lazy comatch c : a !comonad with
   | c#Left  -> repeat y
   | c#Proj  -> x
   | c#Right -> repeat y

let comonad_abstract_dispatch :
  type a o.
  ((a query, a) comonad -> a)
  -> ((a !stream query, a) comonad -> a !stream)
  -> ((o query, a) comonad -> o)
  = fun on_proj on_direction -> function
    | Proj -> on_proj Proj
    | Left -> on_direction Left
    | Right -> on_direction Right

let go : type a.
  (a !stream query, a) comonad -> (a !comonad -> a !stream) -> (a !comonad -> a !stream)
  -> a !comonad -> a !comonad = fun direction fwd bwd com ->
  let bs = comatch s : a !stream with s # Head -> proj com | s # Tail -> bwd com in
  let fs = com |> fwd |> tail in
  let dispatch : type o. (o query, a) comonad -> o = fun o ->
  comonad_abstract_dispatch
    (fun _ -> com |> fwd |> head)
    (fun direction' -> if direction = direction' then fs else bs
    ) o
  in
  COMONAD { dispatch }

let go_left  s = go Left left right s
let go_right s = go Right right left s

let rec map_iterate : type a b. (a -> b) -> (a -> a) -> a -> b !stream
  = fun f shift c -> lazy comatch s : b !stream with
| s#Head -> f c
| s#Tail -> map_iterate f shift (shift c)

let cobind : type a b. (a !comonad -> b) -> a !comonad -> b !comonad =
  fun f c -> lazy comatch com : b !comonad with
| com#Left -> map_iterate f go_left (go_left c)
| com#Proj -> f c
| com#Right -> map_iterate f go_right (go_right c)

let rule (c: bool !comonad) =
  let left  = proj (go_left c)
  and middle = proj c
  and right = proj (go_right c) in
  not (left && middle && not right || (left = middle))

let rec fold
: type a. (a -> a) -> a -> a !stream
= fun f a -> comatch r : a !stream with
| r#Head -> a
| r#Tail -> fold f (f a)

let game_of_life = fold (cobind rule) (point true false)

let print c =
  let r = ref c in
  for i = 1 to 20 do r := go_left !r done;
  for i = 1 to 40 do
    print_char (if proj !r then '#' else '.');
    r := go_right !r
  done;
  print_newline ()

let show, et_show = bench (fun () ->
  for i = 1 to 10 do
    print (nth i game_of_life)
  done)

let _ = Printf.printf "In %f seconds.\n" et_show

end
