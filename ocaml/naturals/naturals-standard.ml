(*
  Implementation for the naturals datatype.

  Builtin integers.
*)


type nat = Zero | Suc of nat

let zero = Zero
let succ n = Suc n

let rec add m n = match n with
    Zero   -> m
  | Suc n' -> succ (add m n')

let rec mul m n = match n with
    Zero   -> Zero
  | Suc n' -> add (mul m n') m
