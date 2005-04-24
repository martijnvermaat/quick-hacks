(*
  Implementation for the booleans datatype.

  Using datatype with two constructors.
*)


type bool' = True | False


let true'  = True
let false' = False


let and' b1 b2 = match b1 with
    True  -> b2
  | False -> False

let not' b = match b with
    True  -> False
  | False -> True

let or' b1 b2 = not' (and' (not' b1) (not' b2) )
