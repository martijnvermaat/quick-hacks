(*
  Implementation for the naturals datatype.

  With length of lists.
*)


(*
  A natural == list of empty lists
  where the length of the list is the value.

  A list of empty lists need not have an
  explicit type, but we have to use one
  because we can't use unbound type variables.
  So we just use int, although we will use no
  integers here.
*)
type nat = int list list

let zero  = []
let suc n = []::n

let add = (@) (* append *)

(*
  This is a trick. Every element in list m
  gets replaced by list n.
  After that, we just have to flatten the
  resulting list and we have 'multiplied'.
*)
let mul m n = List.flatten (List.map (fun l -> n) m)
