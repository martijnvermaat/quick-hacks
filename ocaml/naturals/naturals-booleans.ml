(*
  Implementation for the naturals datatype.

  Builtin booleans.
*)


type nat = bool

let zero = false
let suc = not

let add = (||)

let mul = (&&)
