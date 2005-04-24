(*
  Specification for the booleans datatype.

  All exported names are postfix by ' to avoid
  clashes with built-in booleans.
*)


(*
  Boolean datatype.
*)
type bool'


(*
  Constructors.
*)
val true'  : bool'
val false' : bool'


(*
  Boolean operators.
*)
val and' : bool' -> bool' -> bool'
val or'  : bool' -> bool' -> bool'
val not' : bool' -> bool'
