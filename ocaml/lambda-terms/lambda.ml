(*
  Lambda calculus terms in OCaml
  Implementation
*)


(* A term is a variable, abstraction or application. *)

type term =
    Var of string
  | Abs of string * term
  | App of term * term


(* Some wrapper functions for term constructors. *)
let var s = Var(s)
let abs s t = Abs(s, t)
let app t u = App(t, u)


(* show returns the string representation of a term. *)
(*
  Note: we could do better in placing parentheses.
*)

let rec term_to_string = function
    Var(s)    -> s
  | Abs(s, t) -> "\\" ^ s ^ ". " ^ (term_to_string t)
  | App(t, u) -> "(" ^ (term_to_string t) ^ ") (" ^ (term_to_string u) ^ ")"


(* List free variables. *)

let rec free_vars = function
    Var(s)    -> [s]
  | Abs(s, t) -> List.filter (fun x -> x <> s) (free_vars t)
  | App(t, u) -> List.append (free_vars t) (free_vars u)


(* Generate fresh variable (not in l). *)

let rec fresh_var v l =
  if List.mem v l then   (* find fresh var *)
    fresh_var (v ^ "'") l
  else
    v                    (* v is fresh *)


(* Substitution, substitute term for var in argument. *)

let rec substitute var term = function
    Var(s)    -> if s = var then term else Var(s)
  | Abs(s, t) ->
      let f_t = free_vars t in
      let f_term = free_vars term in
        if (s = var) then                         (* var got bound *)
          Abs(s, t)
        else if (not (List.mem var (f_t))) then   (* nothing to do *)
          Abs(s, t)
        else if (List.mem s (f_term)) then        (* rename bound vars *)
          let f = fresh_var s (List.append (f_t) (f_term)) in
            Abs(f, substitute var term t)
        else                                      (* regular substitution *)
          Abs(s, substitute var term t)
  | App(t, u) -> App(substitute var term t,
                     substitute var term u)


(* Test for possible beta reduction. *)

let is_redex = function
    App(Abs(s, t), u) -> true
  | _ -> false


(* Beta reduction rule. *)

let beta_reduce = function
    App(Abs(s, t), u) -> substitute s u t
  | t -> t


(* Apply one beta reduction step in term. *)
(*
  Note: here (and in the normalize function) we could
  also use a 'has_redex' function instead of the check
  on equality after applying normalize_step.
  This is actually the approach taken where we use the
  is_redex function (we could also do an equality check
  there after applying beta_reduce).
  Maybe we should stick to one way of doing things, and
  add a 'has_redex' function.
*)

let rec normalize_step t =
  if is_redex t then
    beta_reduce t
  else
    match t with
        Var(s)    -> Var(s)
      | Abs(s, t) -> Abs(s, normalize_step t)
      | App(t, u) ->
          let n_t = normalize_step t in
            if n_t = t then normalize_step u
            else n_t


(* Normalize term. *)

let rec normalize t =
  let n_t = normalize_step t in
    if n_t = t then t
    else normalize_step n_t


(* Test if two terms are alpha convertible. *)
(*
  Note: this is actually a nice excercise for regular
  Lambda terms, but we won't try to find an ugly hack
  for this.
  On debruijn terms on the other hand, this operation
  is much easier. Therefore it would be nice to have
  a debruijn representation of terms and convert terms
  first.
*)
(*
  Note: maybe the following is an idea to implement
  this operation on regular Lambda terms. Add a third
  parameter which is a list of pairs translating vars
  of the first term to vars of the second.
  On second thought this seems like an optimization of
  the more general approach of trying to alpha-convert
  the first term to the second term (on each recursive
  call, apply a substitution if we see an abstraction.
*)
(*
  The following is an implementation of alpha
  convertibility following the latter approach above.
  There may be errors in this algorithm, it has not
  been thought over very well ;)
*)

let rec alpha_convertible term = function
    Var(s) ->
      begin
        match term with
            Var(s') -> s = s'
          | _       -> false
      end
  | Abs(s, t) ->
      begin
        match term with
            Abs(s', t') ->
              if s = s' then
                alpha_convertible t t'
              else
                alpha_convertible t
                  (substitute s' (Var(s)) t')
          | _ -> false
      end
  | App(t, u) ->
      match term with
          App(t', u') ->
            alpha_convertible t t'
            && alpha_convertible u u'
        | _ -> false




(*
  Opgave:
  Voeg normalizatie toe, dus een functie

    val normalize : term -> term

  die een term beta reduceert naar normaalvorm en het
  resultaat terug geeft. Je mag zelf kiezen welke
  normalizatie strategie je gebruikt, maar je moet wel
  aangeven welke keuze je hebt gemaakt.
*)
