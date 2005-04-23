(*
  This is a solution to the countdown problem
  in OCaml.

  The countdown problem is described by Graham
  Huttonin his Functional Pearls column of the
  Journal of Functional Programming [1].

  This code is a direct translation of the
  Haskell solution given by Hutton in the same
  column.

  The Haskell solution makes heavy use of
  list comprehensions. Since OCaml doesn't
  have them, this code is at some places a
  bit less elegant.


  Example problem instance:

    Numbers (1,3,7,10,25,50) with 765 should
    yield:

    (((25-7)-3)*(1+50))
    ((25-(3+7))*(1+50))
    (((25-3)-7)*(1+50))
    ((25-10)*(1+50))
    (3*((7*(50-10))-25))
    [...]


  Usage:

    $ ocaml countdown.ml

    or

    $ ocamlc -o countdown countdown.ml
    $ ./countdown


  April 2005, Martijn Vermaat

  This code is based on the work by Graham
  Hutton and available as Open Source under
  the new BSD License:
  http://www.opensource.org/licenses/bsd-license.php


  [1] Hutton, G. (2002) Functional Pearl: the
  countdown problem. Journal of Functional
  Programming.
  http://www.cs.nott.ac.uk/~gmh/countdown.pdf
*)



(************************************************
  Implementation
************************************************)


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
  Applying operator o to operands m and n
  yields a natural number. (Optimized.)
*)
let valid' o m n = match o with
    Add -> (m <= n)
  | Sub -> (m > n)
  | Mul -> (m <> 1) && (n <> 1) && (m <= n)
  | Div -> (n <> 1) && (m mod n) = 0


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
            if valid' o e1' e2' then
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



(************************************************
  Below is the first optimization as suggested
  by Hutton.
************************************************)


(*
  This optimization is a real must-have in
  languages with strict evaluation like OCaml
  (and unlike Haskell).
  Invalid expressions are now filtered out
  earlier, so there will not be a lot of time
  spent on evaluating them.
  In a lazy language, a lot of this work will
  be suspended (but the optimization is still
  worth quite a bit).
*)


(*
  A result is an expression and its evaluation.
*)
type result = (expression * int)


(*
  Return list of possible results for list of
  natural numbers l.
  Excuse me for the (especially in this function)
  unreadable source code due to the flatten's and
  map's. I tried to translate the list
  comprehensions of Hutton as directly as
  possible. I admit this is ugly.
*)
let rec results l = match l with
    []  -> []
  | [n] -> if n > 0 then [(Val n, n)] else []
  | _   ->

      (*
        List of possible results of applying an
        operator to l and r.
      *)
      let combine (l, x) (r, y) =
        let ops = [Add; Sub; Mul; Div] in
          List.map
            (fun o -> (App(o, l, r), apply o x y))
            (List.filter (fun o -> valid' o x y) ops)
      in

      (*
        List of all possible results of combining
        an element of ls with an element of rs.
      *)
      let combined_results (ls, rs) =
        List.flatten
          (List.map
             (fun lx ->
                List.flatten
                  (List.map (fun ry -> combine lx ry) (results rs)))
             (results ls))
      in

        List.flatten
          (List.map
             combined_results
             (ne_split l))


(*
  A list of expressions over numbers that yield
  number on evaluation.
*)
let solutions' numbers number =

  (*
    A list of all 'good' expressions over values
    of list l.
  *)
  let exprs l =
    let check (e, m) = (m = number) in
    List.map (fun (e, m) -> e) (List.filter check (results l))
  in

    List.flatten (List.map exprs (subbags numbers))



(************************************************
  What is left is a way to work with al this.
************************************************)


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
          begin
            match l with
                Val _ -> expression_to_string l
              | _     -> "(" ^ (expression_to_string l) ^ ")"
          end
          ^ " " ^ (operator_to_string o) ^ " " ^
          begin
            match r with
                Val _ -> expression_to_string r
              | _     -> "(" ^ (expression_to_string r) ^ ")"
          end


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
    flush stdout;

    let print e =
      print_string (expression_to_string e);
      print_newline ()
    in
    let s = solutions' !numbers number in
      List.iter print (solutions' !numbers number);
      if List.length s > 1 then
        begin
          print_string "This were ";
          print_int (List.length s);
          print_string " solutions.\n"
        end
      else if List.length s = 1 then
        print_string "This was the only solution.\n"
      else
        print_string "Sorry, there are no solutions to this problem.\n"


(*
  Start main program.
*)
let _ = countdown ()
