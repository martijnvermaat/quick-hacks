(*
   Lambda calculus terms in OCaml
   Interface
 *)


type term =
    Var of string
  | Abstraction of string * term
  | Application of term * term

val show : term -> string

val substitute : string -> term -> term -> term

val reduce : term -> term

val isredex : term -> bool
