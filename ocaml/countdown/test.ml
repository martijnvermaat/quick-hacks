(*
let rec sum n =
  if n = 0 then []
  else n::(sum (n-1))

let rec take n l = match n with
    0 -> []
  | n -> match l with
        []    -> raise (Failure "take")
      | x::xs -> x::(take (n-1) xs)

let rec sublists l = match l with
    []    -> [[]]
  | x::xs ->
      let len = List.length l in
        (List.map (fun n -> take n l) (List.rev (sum len)))
        @ (sublists xs)
*)

let rec sublists l = match l with
    []    -> [[]]
  | x::xs ->
      (sublists xs) @
        (List.map (fun l -> x::l) (sublists xs))

let rec insertions e l = match l with
    []    -> [[e]]
  | x::xs -> (e::x::xs) :: (List.map (fun l -> x::l) (insertions e xs))

let rec permutations l = match l with
    []    -> [[]]
  | x::xs ->
      List.flatten
        (List.map (fun l -> (insertions x l)) (permutations xs))

let subbags l =
  List.flatten
    (List.map (permutations) (sublists l))

type operator = Add | Sub | Mul | Div

let valid o n m = match o with
    Add -> true
  | Sub -> (n > m)
  | Mul -> true
  | Div -> (n mod m) = 0

let apply o n m = match o with
    Add -> n + m
  | Sub -> n - m
  | Mul -> n * m
  | Div -> n / m

type expression =
    Val of int
  | App of operator * expression * expression

let rec values e = match e with
    Val i          -> [i]
  | App(_, e1, e2) -> (values e1) @ (values e2)

(* Note:
   Failure within eval is handled by returning a
   list of results, with the convention that a
   singleton list denotes success, and the empty
   list denotes failure.
   Kunnen we dit niet eleganter met een exception
   doen? *)
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

let solution e numbers number =
  (List.mem (values e) (subbags numbers))
  && ((eval e) = [number])

let rec split l = match l with
    []    -> [([], [])]
  | x::xs ->
      ([], l) ::
        (List.map (fun (l, r) -> (x::l, r)) (split xs))

let ne_split l =
  let no_empty (l, r) = not(l=[] || r=[]) in
    List.filter no_empty (split l)

(* Given two lists, return list of all pairs
   that are a combination of two elements of
   the list. *)
let rec combine l1 l2 = match l1 with
    []    -> []
  | x::xs ->
      (List.map (fun e -> (x,e)) l2)
        @ (combine xs l2)

(* Generate all possible expressions over
   numbers in list. *)
let rec expressions l = match l with
    []  -> []
  | [n] -> [Val n]
  | _   ->
      let aps (l, r) = [App(Add, l, r);
                            App(Sub, l, r);
                            App(Mul, l, r);
                            App(Div, l, r)] in
      let pairs =
        let make_exprs (l, r) = (expressions l), (expressions r) in
          List.map make_exprs (ne_split l)
      in
      let pairs' = List.map (fun (l, r) -> combine l r) pairs in
        List.flatten (List.map aps (List.flatten pairs'))

let solutions numbers number =
  List.filter (fun e -> (eval e) = [number]) 
    (List.flatten (List.map expressions (subbags numbers)))


let rec expression_to_string e = 
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

let yo numbers number =
  let print e =
    print_string (expression_to_string e);
    print_newline ();
  in
    List.iter print (solutions numbers number)


(* Testing materials... *)
let e = App(Sub, Val 10, Val 3)
let e' = App(Mul, App(Sub, Val 10, Val 3), Val 23)
let nums = [3;7;11;15]

(*
  Example:

  # yo nums 10;;
  (3+7)
  (7+3)
  ((3*7)-11)
  ((7*3)-11)
  - : unit = ()

*)
