(*
  Implementation for the tape datatype.

  A tape is an infinite (in two directions) list of cells, of which a
  finite number is 1 and an infinite number is blank.

  This representation is a mapping from integers Z to states {B,1}.
*)


type symbol = int option
type position = int
type direction = Left | Right

module PositionMap = Map.Make(struct
                                type t = position
                                let compare = compare
                              end)

type cells = int PositionMap.t
type tape = cells * position

let empty_tape = (PositionMap.empty, 0)

let rec set_symbol cells symbol position =
  match symbol with
      Some v -> PositionMap.add position v cells
    | None   -> PositionMap.remove position cells

let load_tape symbols =
  let (cells, position) = empty_tape in
  let rec set_symbols cells symbols position =
    match symbols with
        []               -> cells
      | symbol::symbols' -> set_symbols (set_symbol cells symbol position) symbols' (position + 1)
  in
    ((set_symbols cells symbols 0), position)

let do_step tape symbol direction =
  let (cells, position) = tape in
  let new_position = match direction with
      Left  -> position - 1
    | Right -> position + 1
  in
    ((set_symbol cells symbol position), new_position)

let get_symbol tape position =
  let (cells, _) = tape in
    try
      Some (PositionMap.find position cells)
    with
        Not_found -> None

let current_symbol tape =
  let (_, position) = tape in
    get_symbol tape position

(*
let get_tape tape =
  let rec make_list low high =
    if (low < high) then
      (get_symbol tape low) :: (make_list (low + 1) high)
    else
      []
  in
  let (cells, position) = tape in
  let before = make_list (PositionSet.min_elt (PositionSet.add position cells)) position
  and after = make_list position (PositionSet.max_elt (PositionSet.add position cells))
  in
    before, (get_symbol tape position), after
*)

let get_tape tape =
  let cells, position = tape
  in
  let rec blanks n = (* todo: ExtList.List.Make *)
    if (n > 0) then
      None :: (blanks (n - 1))
      else
        []
  in
  let combine position symbol (list, last) =
      ((list @ (blanks (position - last - 1)) @ [Some symbol]), position)
  in
  let (c, p) = PositionMap.fold combine cells ([], (position - 1))
  in
  let l = c @ (blanks (position - p))
  in
  let rec take n l =
    match n, l with
        0, _      -> []
      | _, []     -> []
      | _, (h::t) -> h :: take (n - 1) t
  in
  let rec drop n l =
    match n, l with
        0, _ -> l
      | _, [] -> []
      | _, h::t -> drop (n - 1) t
  in
  let q = (List.length l) - (max p position) + position - 1
  in
    (take q l), (List.nth l q), (drop (q + 1) l)
