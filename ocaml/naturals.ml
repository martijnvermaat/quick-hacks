(*
 Peano arithmetic in OCaml
 Martijn Vermaat, 2005-03-30
*)

(* A natural is zero or the succesor of a natural. *)
type natural = Zero | Succ of natural;;

(* show returns the integer value for a natural. *)
let rec show = function
    Zero    -> 0
  | Succ(n) -> 1 + (show n);;

(* Addition on naturals. *)
let rec add = function
    Zero    -> fun m -> m
  | Succ(n) -> fun m -> add n (Succ(m));;

(* Multiplication on naturals. *)
let rec mul = function
    Zero    -> fun m -> Zero
  | Succ(n) -> fun m -> add m (mul n (m));;

(* Todo: define add, mul, pow, in such a way their
   symmetry is clear. *)


(* Test our datatype. *)

print_string "Should print 3:\n";;
print_int (show (Succ(Succ(Succ(Zero)))));;
print_newline ();;

print_string "Should print 3+2=5:\n";;
print_int (show (add (Succ(Succ(Succ(Zero)))) (Succ(Succ(Zero))) ));;
print_newline ();;

print_string "Should print 3*2=6:\n";;
print_int (show (mul (Succ(Succ(Succ(Zero)))) (Succ(Succ(Zero))) ));;
print_newline ();;
