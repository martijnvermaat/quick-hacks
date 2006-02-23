(*
  Propositional logic formulae in OCaml
*)


type formula =
    Var of string
  | And of formula * formula
  | Or of formula * formula
  | Imp of formula * formula
  | Not of formula


let rec to_string = function
    Var(s)      -> s
  | And(f1, f2) -> "(" ^ (to_string f1) ^ " /\\ " ^ (to_string f2) ^ ")"
  | Or(f1, f2)  -> "(" ^ (to_string f1) ^ " \\/ " ^ (to_string f2) ^ ")"
  | Imp(f1, f2) -> "(" ^ (to_string f1) ^ " -> " ^ (to_string f2) ^ ")"
  | Not(f)      -> "(! " ^ (to_string f) ^ ")"


let rec eval v = function
    Var(s)      -> v s
  | And(f1, f2) -> (eval v f1) && (eval v f2)
  | Or(f1, f2)  -> (eval v f1) || (eval v f2)
  | Imp(f1, f2) -> (eval v f2) || not (eval v f1)
  | Not(f)      -> not (eval v f)


let f1 = Or(Var("a"), Var("b"))
let f2 = Or(Var("a"), Not(Var("a")))
let f3 = Imp(Var("b"), Not(Var("b")))

let v1 s =
  if s = "b" then true else false

let _ =

  print_string "f1: ";
  print_string (to_string f1);
  print_newline ();

  print_string "f2: ";
  print_string (to_string f2);
  print_newline ();

  print_string "f3: ";
  print_string (to_string f3);
  print_newline ();

  print_string "f1: ";
  print_string (string_of_bool (eval v1 f1));
  print_newline ();

  print_string "f2: ";
  print_string (string_of_bool (eval v1 f2));
  print_newline ();

  print_string "f3: ";
  print_string (string_of_bool (eval v1 f3));
  print_newline ();
