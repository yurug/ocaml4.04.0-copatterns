(* I. Introduction *)

type nat = Zero | Succ of nat

type 'a _stream = ('a cell) Lazy.t and 'a cell = Cell of 'a * 'a _stream

let rec from : nat -> nat _stream = fun n -> lazy (Cell (n, from (Succ n)))

let naturals = from Zero

let rec nth : nat -> 'a _stream -> 'a = fun n s ->
  let Cell (hd, tl) = Lazy.force s in
  match n with
  | Zero -> hd
  | Succ m -> nth m tl

type 'a stream = {
  Head : 'a;
  Tail : 'a stream;
}

let corec from : nat -> nat stream with
  | (.. n)#Head -> Zero
  | (.. n)#Tail -> from (Succ n)

let rec nth n s = match n with
  | Zero -> s#Head
  | Succ m -> nth m s#Tail


let corec map2 : type a b c. (a -> b -> c) -> a stream -> b stream -> c stream with
  | (.. f s1 s2)#Head -> f s1#Head s2#Head
  | (.. f s1 s2)#Tail -> map2 f s1#Tail s2#Tail

(* III. Constructions avancées du filtrage par comotifs *)

let corec fib : int stream with
   | ..#Head -> 0
   | ..#Tail : int stream with
   | ..#Tail#Head -> 1
   | ..#Tail#Tail -> map2 ( + ) fib fib#Tail

let corec lazy fib : int stream with
   | ..#Head -> 0
   | ..#Tail : int stream with
   | ..#Tail#Head -> 1
   | ..#Tail#Tail -> map2 ( + ) fib fib#Tail

let corec cycle : nat -> nat stream with
   | (.. n)#Head -> n
   | (.. Zero)#Tail -> cycle (Succ (Succ (Succ Zero)))
   | (.. (Succ m))#Tail -> cycle m

type zero = Z and 'a succ = S

type 'a fuel =
  | Dry : zero fuel
  | More :  'a fuel -> ( 'a succ) fuel

type ('a,'b) bounded_iterator = {
  GetVal :  'a;
  Next : ('a,'b) bounded_iterator <- ('a, 'b succ) bounded_iterator;
}

module type Seq = sig
  type 'a t
  val head : 'a t -> 'a
  val tail : 'a t -> 'a t
end

module MkIterator (S : Seq) = struct
  let corec wrap : type a b.a S.t -> b fuel -> (a, b) bounded_iterator with
     | (.. l n)#GetVal -> S.head l
     | (.. l (More n))#Next -> wrap (S.tail l) n
end

(* IV. Destructeurs de premier ordre et première classe *)

type _loc = {name: string; x : int; y : int}

let select_name  lc = lc.name   and update_name  s lc = {lc with name = s}
let select_x     lc = lc.x      and update_x     b lc = {lc with x = b}
let select_y     lc = lc.y      and update_y     n lc = {lc with y = n}

type loc = {Name : string; X : int; Y: int}

let select (d : 'a loc_obs) (Loc {dispatch} : loc) : 'a = dispatch d

type (_,_) eq = Eq : ('a,'a) eq

let eq_loc : type a b. a loc_obs * b loc_obs -> ((a,b) eq) option = function
  | (Name, Name) -> Some Eq
  | (X, X) -> Some Eq
  | (Y, Y) -> Some Eq
  | _ -> None

let update (type a) (d1 : a loc_obs) (x : a) (Loc {dispatch}) =
   let dispatch : type o. o loc_obs -> o = fun d2 -> match eq_loc (d1,d2) with
     | Some Eq -> x
     | _ -> dispatch d2
   in Loc {dispatch}
