(*
  Implementation for the tape datatype.

  A tape is an infinite (in two directions) list of cells, of which a
  finite number is 1 and an infinite number is blank.

  This representation is a mapping from integers Z to states {B,1}.
*)


type symbol = Blank | One
type position = int
type direction = Left | Right

module PositionSet = Set.Make(struct
                                type t = position
                                let compare = compare
                              end)

type cells = PositionSet.t
type tape = cells * position

let empty_tape = (PositionSet.empty, 0)

let rec set_symbol cells symbol position =
  match symbol with
      Blank -> PositionSet.remove position cells
    | One   -> PositionSet.add position cells

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
  let (cells, position) = tape in
    if PositionSet.mem position cells then
      One
    else
      Blank

let current_symbol tape =
  let (_, position) = tape in
    get_symbol tape position

(* todo: fix if there are no 1 cells *)
let get_tape tape =
  let rec make_list low high =
    if (low < high) then
      (get_symbol tape low) :: (make_list (low + 1) high)
    else
      []
  in
  let (cells, position) = tape in
  let before = make_list (PositionSet.min_elt cells) position
  and after = make_list position (PositionSet.max_elt cells)
  in
    before, (get_symbol tape position), after


(* below is for other file *)

type state = int
type rule = state * symbol * state * symbol * direction
type machine = rule list * state * tape

let rules = [(1, One, 1, Blank, Right);
             (1, Blank, 0, Blank, Right)]

let do_step' machine =
  let (rules, state, tape) = machine in
  let (_, _, s, c, d) = List.find (fun (s, c, _, _, _) -> s = state && c = (current_symbol tape)) rules in
    rules, s, (do_step tape c d)
