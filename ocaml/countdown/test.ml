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

let rec insertions e l = match l with
    []    -> [[e]]
  | x::xs -> (e::x::xs) :: (List.map (fun l -> x::l) (insertions e xs))

let rec permutations = true
