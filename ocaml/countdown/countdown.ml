(*
  This is a solution to the countdown problem
  in OCaml.

  The countdown problem is described by Graham
  Huttonin the Functional Pearls column of the
  Journal of Functional Programming [1].

  This code is a direct translation of the
  Haskell solution given by Hutton in the same
  column.

  The Haskell solution makes heavy use of
  list comprehensions. Since OCaml doesn't
  have them, this code is at some places a
  bit less elegant.


  Example problem instance:
    Numbers (3,7,11,15) with 10 should yield:
    (7+3)
    (3+7)
    ((7*3)-11)
    ((3*7)-11)


  Usage:

    $ ocaml countdown.ml

    or

    $ ocamlc -o countdown countdown.ml
    $ ./countdown


  Future:
  This is a naive brute-force solution. Two
  optimizations are suggested by Hutton that
  should be not too hard to translate to
  this code.


  April 2005, Martijn Vermaat

  [1] http://www.cs.nott.ac.uk/~gmh/countdown.pdf
*)



(*
  Return a list of all permutations of al
  sublists lf l.
*)
let subbags l =

  (*
    Return a list of all sublists of l.
  *)
  let rec sublists l = match l with
      []    -> [[]]
    | x::xs ->
        (sublists xs) @
          (List.map (fun l -> x::l) (sublists xs))
  in

  (*
    Return a list of all possible lists resulting
    from inserting e in l.
  *)
  let rec insertions e l = match l with
      []    -> [[e]]
    | x::xs -> (e::x::xs) :: (List.map (fun l -> x::l) (insertions e xs))
  in

  (*
    Return a list of all permutations of l.
  *)
  let rec permutations l = match l with
      []    -> [[]]
    | x::xs ->
        List.flatten
          (List.map (fun l -> (insertions x l)) (permutations xs))
  in

  List.flatten
    (List.map (permutations) (sublists l))


(*
  Binary operators to use.
*)

type operator = Add | Sub | Mul | Div


(*
  Applying operator o to operands m and n
  yields a natural number.
*)
let valid o m n = match o with
    Add -> true
  | Sub -> (m > n)
  | Mul -> true
  | Div -> (m mod n) = 0


(*
  Result of applying operator o to operands
  m and n.
*)
let apply o m n = match o with
    Add -> m + n
  | Sub -> m - n
  | Mul -> m * n
  | Div -> m / n


(*
  An expression is a single natural number or
  an application of an operator to two operands.
*)
type expression =
    Val of int
  | App of operator * expression * expression


(*
  Return a list of all natural numbers used in
  expression e.
*)
let rec values e = match e with
    Val i          -> [i]
  | App(_, e1, e2) -> (values e1) @ (values e2)


(*
  Result of evaluating expression e.
  
  Quote from Hutton:
    "Failure within eval is handled by returning
    a list of results, with the convention that a
    singleton list denotes success, and the empty
    list denotes failure."

  Maybe it is more elegant to handle this with
  exceptions.
*)
let rec eval e = match e with
    Val i ->
      if i > 0 then [i] else []
  | App(o, e1, e2) ->
      match (eval e1, eval e2) with
          ([e1'], [e2']) ->
            if valid o e1' e2' then
              [apply o e1' e2']
            else
              []
        | _ -> []


(*
  Expression e is a solution to the problem with
  numbers and number.
*)
let solution e numbers number =
  (List.mem (values e) (subbags numbers))
  && ((eval e) = [number])


(*
  Return a list of all pairs (l,r) where l and r
  appended yield the list l and l and r are not
  empty.
*)  
let ne_split l =

  (*
    Return a list of all pairs (l,r) where l and r
    appended yield the list l.
  *)
  let rec split l = match l with
      []    -> [([], [])]
    | x::xs ->
        ([], l) ::
          (List.map (fun (l, r) -> (x::l, r)) (split xs))
  in

  (*
    Lists l and r are both not empty.
  *)
  let no_empty (l, r) = not(l=[] || r=[])
  in

    List.filter no_empty (split l)


(*
  Generate a list of all possible expressions
  over the natural numbers in list l.
*)
let rec expressions l = match l with
    []  -> []
  | [n] -> [Val n]
  | _   ->

      (*
        A list of applying each operator to l
        and r.
      *)
      let aps (l, r) = [App(Add, l, r);
                        App(Sub, l, r);
                        App(Mul, l, r);
                        App(Div, l, r)]
      in

      (*
        Given two lists L1 and L2, return a list of all
        pairs (l,r) where l is an element of L1 and r
        is an element of L2.
      *)
      let rec combine l1 l2 = match l1 with
          []    -> []
        | x::xs ->
            (List.map (fun e -> (x,e)) l2)
            @ (combine xs l2)
      in

      (*
        A list of pairs (l1,l2) where l1 is a list
        of all expressions over a non-empty left
        sublist of l and l2 a list of all
        expressions over the remaining non-empty
        right sublist of l.
      *)
      let pairs =
        let make_exprs (l, r) = (expressions l), (expressions r) in
          List.map make_exprs (ne_split l)
      in

      (*
        A nested list of pairs (l,r) where (l,r)
        is a combination of two elements from the
        list pairs (defined above).
      *)
      let pairs' = List.map (fun (l, r) -> combine l r) pairs
      in

        List.flatten (List.map aps (List.flatten pairs'))


(*
  A list of expressions using only values from
  numbers and whose evaluated value is number.
*)
let solutions numbers number =
  List.filter (fun e -> (eval e) = [number]) 
    (List.flatten (List.map expressions (subbags numbers)))


(*
  String representation of expression e.
*)
let rec expression_to_string e = 

  (*
    String representation of operator o.
  *)
  let operator_to_string o = match o with
      Add -> "+"
    | Sub -> "-"
    | Mul -> "*"
    | Div -> "/"
  in

    match e with
        Val n        -> string_of_int n
      | App(o, l, r) ->
          "(" ^ (expression_to_string l)
          ^ (operator_to_string o)
          ^ (expression_to_string r) ^ ")"


(*
  Reads a number and a list of numbers from
  stdin and prints all solutions to that
  instance of the countdown problem.
*)
let countdown () =

  print_string "The Countdown Problem\n";
  print_string "Please enter a positive natural number: ";

  let number = try read_int () with
      End_of_file ->
        print_string "You quit too soon.\n";
        exit 1
    | Failure _ ->
        print_string "That's not a number.\n";
        exit 1
  in

  let numbers = ref [] in

  let rec loop () =
    match read_int () with
        0 -> ()
      | n ->
          numbers := n :: !numbers;
          try loop () with
              End_of_file -> ()
  in

    print_string "Please enter some positive natural numbers ";
    print_string "(each on its own line) ending\n";
    print_string "with 0 or end-of-file:\n";

    begin
      try loop () with
          End_of_file ->
            print_string "You quit too soon.\n";
            exit 1
        | Failure _ ->
            print_string "That's not a non-empty list of numbers.\n";
            exit 1
    end;

    print_string "I can make ";
    print_int number;
    print_string " from these numbers in the following ways:\n";

    let print e =
      print_string (expression_to_string e);
      print_newline ()
    in
      List.iter print (solutions !numbers number)


(*
  Start main program.
*)
let _ = countdown ()
