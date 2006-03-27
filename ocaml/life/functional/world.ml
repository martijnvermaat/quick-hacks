(*
  Implementation for the world datatype.

  A world contains cells and reflects a state in Conways Game of Life.
  Some operations on worlds are provided to do calculations on them.
*)


(*
  A cell is a pair stating its state and position in the world.
*)
type state    = Living | Dead
type position = int * int
type cell     = state * position


(*
  This creates the type for a set of positions.
*)
module PositionSet = Set.Make(struct
                                type t = position
                                let compare = compare
                              end)


(*
  A world is given by a set of positions that denote the living cells in the
  world. There are no bounds on the size of the world.
  Idea taken from
    http://homepages.inf.ed.ac.uk/dts/fps/pract3-2004/pract3.sml
*)
type world = PositionSet.t


(*
  Add all positions in given list to the given set.
*)
let rec add_all list set =
  match list with
      []   -> set
    | h::t -> add_all t (PositionSet.add h set)


(*
  List of neighbour positions for given position.
*)
let neighbour_positions (x, y) =
  [(x,   y+1);
   (x+1, y+1);
   (x+1, y  );
   (x+1, y-1);
   (x,   y-1);
   (x-1, y-1);
   (x-1, y  );
   (x-1, y+1)]


(*
  Number of living neighbours for given position.
*)
let num_neighbours pos world =
  List.fold_left
    (fun n pos ->
       if PositionSet.mem pos world then
         n + 1
       else
         n)
    0
    (neighbour_positions pos)


(*
  Given a world, return set of candidate positions that may be living after
  the next step in evolution.
*)
let candidates world =
  let poss_list = PositionSet.elements world
  in
    add_all (List.flatten (List.map neighbour_positions poss_list)) world


(*
  Constructor for a new world with no living cells.
*)
let new_world = PositionSet.empty


(*
  Calculate changeset for two worlds. This is a list of cells representing
  the difference from world to world'.
  todo: maybe use a Set of cells instead of a list, it's a changeSET after all
*)
let changeset world world' =
  let changed_poss = PositionSet.elements (PositionSet.diff
                                             (PositionSet.union world world')
                                             (PositionSet.inter world world'))
  and pos_to_cell pos =
    if PositionSet.mem pos world' then
      Living, pos
    else
      Dead, pos
  in
    List.map pos_to_cell changed_poss


(*
  Kill or breed a cell at given position.
*)
let toggle_cell pos world =
  if PositionSet.mem pos world then
    PositionSet.remove pos world
  else
    PositionSet.add pos world


(*
  Play one round of the game and return the update world.
*)
let evolve_world world =
  let evolve_position pos =
    match (PositionSet.mem pos world), (num_neighbours pos world) with
        _,    3 -> true
      | true, 2 -> true
      | _       -> false
  in
    PositionSet.filter evolve_position (candidates world)


(*
  Update the world with the cells in the given list.
*)
let rec load_cells cells world =
  match cells with
      []                  -> world
    | (Living, pos)::tail -> load_cells tail (PositionSet.add pos world)
    | (Dead,   pos)::tail -> load_cells tail (PositionSet.remove pos world)
