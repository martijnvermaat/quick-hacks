(*
 Fun with Church numerals
 Martijn Vermaat, 2005-03-16
*)

(* The Church numeral denoting the integer value 0. *)
let zero = fun s -> fun z -> z;;

(*
 (* The lambda abstractions could be replaced with an explicit definition
    with arguments, but the similarities with Lambda Calculus are less
    clear that way. *)
 let zero s z = z;;
*)

(* Some functions on Church numerals. *)
let succ = fun x -> fun s -> fun z -> s (x s z);;
let add  = fun x -> fun y -> fun s -> fun z -> x s (y s z);;
let mul  = fun x -> fun y -> fun s -> x (y s);;

(* Some more Church numerals. *)
let one = succ zero;;
let two = succ one;;
let three = succ two;;
let four = succ three;;
let five = succ four;;

(* show returns integer value denoted by the given Church numeral. *)
let show n =
  let inc n = n + 1 in
  n inc 0;;


(* Asside: These Church numerals could also be
   implemented in their own type. *)


(* Test our Church numerals. *)

print_string "Should print (1+2)*(4+5)=27:\n";;
print_int (show (mul (add one two) (add four five)));;
print_newline ();;
