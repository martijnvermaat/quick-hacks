(*
 Fun with church numerals
 Martijn Vermaat, 2005-03-16
*)

(* The church numeral denoting the integer value 0. *)
let zero = fun s -> fun z -> z;;

(*
 (* The lambda abstractions could be replaced with an explicit definition
    with arguments, but the similarities with Lambda Calculus are less
    clear that way. *)
 let zero s z = z;;
*)

(* Some functions on church numerals. *)
let succ = fun x -> fun s -> fun z -> s (x s z);;
let add  = fun x -> fun y -> fun s -> fun z -> x s (y s z);;
let mul  = fun x -> fun y -> fun s -> x (y s);;

(* Some more church numerals. *)
let one = succ zero;;
let two = succ one;;
let three = succ two;;
let four = succ three;;
let five = succ four;;

(* show returns integer value denoted by the given church numeral. *)
let show n =
  let inc n = n + 1 in
  n inc 0;;


let n = mul (add one two) (add four five)
in print_int (show n);;

print_newline ();;
