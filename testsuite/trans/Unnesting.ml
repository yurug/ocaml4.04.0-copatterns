
type    codata
type 'a query

type nat = Zero | Succ of nat

let rec nat_of_int n = if n = 0 then Zero else Succ (nat_of_int (pred n))
let rec int_of_nat n = match n with
  | Zero -> 0
  | Succ n -> succ (int_of_nat n)

(* User entrance *)

type ('kind,'a) stream =
  | Stream : { dispatch : 'o. ('o query,'a) stream -> 'o } -> (codata,'a) stream
  | Head : ('a query,'a) stream
  | Tail : (((codata,'a) stream) query,'a) stream

(* Getters *)

let head (Stream {dispatch}) = dispatch Head
let tail (Stream {dispatch}) = dispatch Tail


let rec zipWith
  : type a b c.
    (a -> b -> c) ->
    (codata,a) stream -> (codata,b) stream -> (codata,c) stream
  = fun f sa sb ->
    let dispatch
      : type o. (o query,c) stream -> o
      = function
        | Head -> f (head sa) (head sb)
        | Tail -> zipWith f (tail sa) (tail sb)
    in Stream {dispatch}

let rec get n s = if n = 0 then head s else get (pred n) (tail s)

let zeros =
  let rec zeros : (codata,int) stream =
    let dispatch
      : type o . (o query,int) stream -> o
      = function
        | Head -> 0
        | Tail -> zeros
    in Stream {dispatch}
  in zeros


let fib =
  let rec fib : (codata,int) stream =
    let g =
      let dispatch : type o . (o query, int) stream -> o
        = function
          | Head -> 1
          | Tail -> zipWith ( + ) fib (fib |> tail)
      in Stream {dispatch}
    in
    (* entrance *)
    let dispatch
      : type o . (o query,int) stream -> o
      = function
        | Head -> 0
        | Tail -> g
    in Stream {dispatch}
  in fib

(*

let cycle = comatch cyc : nat -> nat !stream with
| (cyc x       )#Head -> x
| (cyc Zero    )#Tail -> cyc limit
| (cyc (Succ n))#Tail -> cyc n

*)

let cycle =
  let rec cyc  : nat -> (codata,nat) stream =
    fun x ->
      let g1 = function
        | Zero   -> cyc (Succ (Succ Zero))
        | Succ n -> cyc n
      in
      let dispatch
        : type o . (o query,nat) stream -> o
        = function
          | Head -> x
          | Tail -> g1 x
      in Stream {dispatch}
  in cyc
