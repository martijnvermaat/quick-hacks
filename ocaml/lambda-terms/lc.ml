(*
   Lambda calculus terms in OCaml
   Implementation
 *)


(* A term is a variable, abstraction or application. *)

type term =
    Var of string
  | Abstraction of string * term
  | Application of term * term;;


(* show returns the string representation of a term. *)

let rec show = function
    Var(s)            -> s
  | Abstraction(s, t) -> "\\" ^ s ^ ". " ^ (show t)
  | Application(t, u) -> "(" ^ (show t) ^ ") (" ^ (show u) ^ ")";;


(* Substitution, substitute term for var in argument. *)
(*
   Note: this definition of substitution is naive, as
   it doesn't rename captured free variables!
*)

let rec substitute var term = function
    Var(s)            -> if (s = var) then term else Var(s)
  | Abstraction(s, t) -> if (s = var) then Abstraction(s, t)
                                      else Abstraction(s, substitute var term t)
  | Application(t, u) -> Application(substitute var term t,
                                     substitute var term u);;


(* Beta reduction. *)

let reduce = function
    Application(Abstraction(s, t), u) -> substitute s u t
  | t -> t;;


(* Test for possible beta reduction. *)

let isredex = function
    Application(Abstraction(s, t), u) -> true
  | _ -> false;;



(* Test our datatype. *)

let omega = Application(
  Abstraction("x", Application(Var("x"),Var("x"))),
  Abstraction("x", Application(Var("x"),Var("x"))));;

let test = Application(Abstraction("x", Application(Var("x"), Var("y"))), Var("y"));;

print_string "Should print (\\x.x x)(\\x.x x):\n";;
print_string (show omega);;
print_newline ();;

print_string "Should print (\\x.x y) y:\n";;
print_string (show test);;
print_newline ();;

print_string "Should print (y y):\n";;
print_string (show (reduce test));;
print_newline ();;
