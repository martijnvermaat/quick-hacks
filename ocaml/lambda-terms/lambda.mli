(*
   Lambda calculus terms in OCaml
   Interface
 *)


type term =
    Var of string            (* variable    *)
  | Abs of string * term     (* abstraction *)
  | App of term * term       (* application *)

val show : term -> string

val substitute : string -> term -> term -> term

val is_redex : term -> bool

val beta_reduce : term -> term

val normalize_step : term -> term

val normalize : term -> term
