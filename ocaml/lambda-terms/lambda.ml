(*
  Lambda calculus terms in OCaml
  Implementation
*)


(* A term is a variable, abstraction or application. *)

type term =
    Var of string
  | Abs of string * term
  | App of term * term


(* show returns the string representation of a term. *)
(*
  Note: we could do better in placing parentheses.
*)

let rec show = function
    Var(s)    -> s
  | Abs(s, t) -> "\\" ^ s ^ ". " ^ (show t)
  | App(t, u) -> "(" ^ (show t) ^ ") (" ^ (show u) ^ ")"


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


(*
  Opgave:
  Voeg normalizatie toe, dus een functie

    val normalize : term -> term

  die een term beta reduceert naar normaalvorm en het
  resultaat terug geeft. Je mag zelf kiezen welke
  normalizatie strategie je gebruikt, maar je moet wel
  aangeven welke keuze je hebt gemaakt.
*)
