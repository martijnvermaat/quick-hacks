(*
  Implementation for the booleans datatype.

  Using powerset over set of elements q.
*)


(*
  Elements in our set.
  (If more than one element, this implementation
  contains 'junk'.)
*)
type elements = A | B | C


(*
  Full set q.
*)
let q = [A;B;C]


(*
  Powerset over q.
*)
type bool' = elements list


(*
  True is entire set, False is empty set.
*)
let true'  = q
let false' = []


(*
  And is intersection.
*)
let and' b1 b2 = List.filter (fun e -> List.mem e b1) b2


(*
  Or is union.
*)
let or' b1 b2 = List.filter (fun e -> (List.mem e b1) || (List.mem e b2)) q


(*
  Not is complement.
*)
let not' b = List.filter (fun e -> not (List.mem e b)) q
