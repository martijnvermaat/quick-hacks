(*
  Implementation for the tape datatype.

  A tape is an infinite (in two directions) list of cells, of which a
  finite contains an integer an infinite number is blank.

  This representation is a mapping from `int' to `int option'.
*)


type symbol    = int option
type position  = int
type direction = Left | Right

module PositionMap = Map.Make(struct
                                type t = position
                                let compare = compare
                              end)

type cells = int PositionMap.t
type tape  = cells * position


(*
  Empty tape.
*)
let empty = (PositionMap.empty, 0)


(*
  Tape constructed from symbols with reading head on first symbol.
*)
let create symbols =
  let f tape symbol = step symbol Right tape in
  let cells, _ = (List.fold f empty symbols) in
  cells, 0


(*
  Update symbol at reading head position and move the reading head.
*)
let step symbol direction tape =
  let cells, position = tape in
  let new_cells =
    match symbol with
      | Some v -> PositionMap.add position v cells
      | None   -> PositionMap.remove position cells
  and new_position =
    match direction with
      | Left  -> direction - 1
      | Right -> direction + 1
  in
  new_cells, new_position


(*
   Symbol at reading head position.
*)
let read tape =
  let cells, position = tape in
  try
    Some (PositionMap.find position cells)
  with
    | Not_found -> None


(*
  Get contents of tape as a triple:
  - list of symbols before the reading head
  - symbol at the reading head
  - list of symbols after the reading head
  TODO: clean up
*)
let contents tape =
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
