type    codata
type 'a query

(* record State S A = state{runState : S → A × S} *)

type ('kind,'s,'a) state =
  | State : { dispatch : 'o. ('o query,'s,'a) state -> 'o } ->
    (codata,'s,'a) state
  | RunState : (('s -> 'a * 's) query,'s,'a) state

let runState (State {dispatch}) = dispatch RunState

(* return : A → State S A *)
(* runState (return a) s = (a, s) *)

(* (return a)#runState s = (a,s) *)

let return
  : type a s. a -> (codata,s,a) state
  = fun a ->
    let dispatch
      : type o. (o query,s,a) state -> o
      = function
        | RunState -> fun s -> (a,s)
    in State {dispatch}


(* _>>=_ : State S A → (A → State S B) → State S B
   runState (m >>= k) s =
     let(a, s') = runState m s
     in runState (k a) s'
*)

(* (bind m k)#runState s = .. *)

let bind
  : type a b s.
    (codata,s,a) state -> (a -> (codata,s,b) state) -> (codata,s,b) state
  = fun m k ->
    let dispatch
      : type o. (o query,s,b) state -> o
      = function
        | RunState -> fun (s : s) ->
          let (b, (s' : s)) = runState m s in
          runState (k b) s'
    in State {dispatch}

let ( >>= ) = bind

(* example *)

type stack = int list

let empty : stack = []

exception EmptyStack

(*
   comatch pop : (stack,int) state with
    | pop#runState (x::xs) → (x,xs)
    | pop#runState []      → raise EmptyStack
 *)

(* unnesting algorithm : need type annotation in g,  *)

let pop : (codata,stack,int) state =
  let aux = function
    | [] -> raise EmptyStack
    | x :: xs -> (x,xs)
  in
  let dispatch
    : type o. (o query,stack,int) state -> o
    = fun RunState -> aux
  in
  State {dispatch}


let pop : (codata,stack,int) state =
  let f = function
  | [] -> raise EmptyStack
  | x :: xs -> (x,xs)
  in
  let dispatch : type o. (o query,stack,int) state -> o = function
    | RunState -> f
  in State {dispatch}

let push n : (codata,stack,unit) state =
  let dispatch : type o. (o query,stack,unit) state -> o
    = fun RunState xs -> ((),n::xs)
  in State {dispatch}

let rec tos : (codata,stack,int) state =
  let dispatch : type o. (o query,stack,int) state -> o = function
    | RunState -> function
        | (x::xs) -> (x,x::xs)
        | _ -> assert false
  in State {dispatch}

let ( *> ) m r = m >>= fun () -> r

let stackManip =
  push 12 *>
  pop >>= fun a ->
  push 23 *>
  pop >>= fun b ->
  push (b - a) >>= fun () ->
  tos

let evalState act m = fst (runState act m)

let execState act m = snd (runState act m)

let main =
  let res = evalState stackManip empty in
  Printf.printf "result : %d\n" res
