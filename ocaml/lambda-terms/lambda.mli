(*
   Lambda calculus terms in OCaml
   Interface
 *)


(* Type of Lambda terms. *)
type term


(* Type of DeBruijn indiced terms. *)
type debruijn


(* Construct terms. *)
val var : string -> term
val abs : string -> term -> term
val app : term -> term -> term


(* Get a string representation of a term. *)
val term_to_string : term -> string


(* Substitution for free variable in term. *)
val substitute : string -> term -> term -> term


(* Beta reduce term to normal form. *)
val normalize : term -> term


(* Test if two terms are equal modulo alpha conversion. *)
val alpha_convertible : term -> term -> bool


(* Get DeBruijn representation of a term. *)
val debruijnize : term -> debruijn


(* String representation of DeBruijn term. *)
val debruijn_to_string : debruijn -> string
