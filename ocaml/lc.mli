(*
   Lambda calculus terms in OCaml
   Interface
 *)


type term

val show : term -> string

val substitute : string -> term -> term -> term

val reduce : term -> term

val isredex : term -> bool
