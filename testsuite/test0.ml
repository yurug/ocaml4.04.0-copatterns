type 'a !stream = {
  Head : 'a ;
  Tail : 'a !stream;
}

(* [0;1;0;1;0...] *)

let zos = comatch zos : int !stream with
| zos#Head -> 0
| zos#Tail#Head -> 1
| zos#Tail#Tail -> zos

(* zipWith without nested copatterns, so we can already implement fibonacci *)

let rec zipWith : (int -> int -> int) -> int !stream -> int !stream -> int !stream
  = fun f sa sb -> comatch zip : int !stream with
| zip#Head -> f (head sa) (head sb)
| zip#Tail -> zipWith ( + ) (tail sa) (tail sb)

(* nested fibonacci *)

let fibonacci = comatch fib : int !stream with
| fib#Head -> 0
| fib#Tail#Head -> 1
| fib#Tail#Tail -> zipWith ( + ) fib (fib |> tail)

(* getter *)

let rec get n s = if n = 0 then head s else get (pred n) (s |> tail)

(* result : 55 ! *)

let () = Printf.printf "result : %d\n" (get 10 fibonacci)
