(*
  Implementation for the booleans datatype.

  Using the integers 0 and 1.
*)


type bool' = int

let true'  = 1
let false' = 0

let and' b1 b2 =  min b1 b2

let not' b = 1 - b

let or' b1 b2 = max b1 b2
