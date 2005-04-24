(*
  Implementation for the booleans datatype.

  Using singleton datatype.
*)


(*
  Singleton algebra.
  (This implementation contains confusion.)
*)
type bool' = B


(*
  True and false are both B (they must be).
*)
let true'  = B
let false' = B


(*
  Operations always return element B.
*)
let and' b1 b2 = B
let or'  b1 b2 = B
let not' b     = B
