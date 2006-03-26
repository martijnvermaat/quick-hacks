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
  A world is given by a width, a height and a set of positions that denote the
  living cells in the world.
  The latter is an idea taken from
    http://homepages.inf.ed.ac.uk/dts/fps/pract3-2004/pract3.sml
*)
type world = int * int * PositionSet.t


(*
  Constructor for a new world with no living cells.
*)
let new_world width height = width, height, PositionSet.empty


(*
  Get the cell at given position.
*)
let cell_at pos world =
  let width, height, cells = world in
    if PositionSet.mem pos cells then
      Living, pos
    else
      Dead, pos


(*
  Add given cell to world, of course overwriting the existing cell at that
  position.
*)
let add_cell cell world =
  let s, pos = cell in
  let width, height, cells = world in
    match s with
        Living -> width, height, PositionSet.add pos cells
      | _      -> width, height, PositionSet.remove pos cells


(*
  Kill or breed a cell at given position.
*)
let toggle_cell pos world =
  match cell_at pos world with
      Living, _ -> add_cell (Dead, pos) world
    | Dead,   _ -> add_cell (Living, pos) world


(*
  Number of living neighbours for given cell.
  todo: de-uglify
*)
let num_neighbours cell world =
  let s, (x, y) = cell in
  let list_of_neighbours =
    [cell_at (x,   y+1) world;
     cell_at (x+1, y+1) world;
     cell_at (x+1, y)   world;
     cell_at (x+1, y-1) world;
     cell_at (x,   y-1) world;
     cell_at (x-1, y-1) world;
     cell_at (x-1, y)   world;
     cell_at (x-1, y+1) world]
  in
    List.fold_left
      (fun n -> function
           (Living, _) -> n + 1
         | _           -> n)
      0
      list_of_neighbours


(*
  What follows is a hacked up implementation of map and iter functions over
  worlds. This should be rewritten.
*)

let rec map_highest_row f width height world =
  if width > 0 then
    map_highest_row f (width-1) height (add_cell (f (cell_at (width-1, height-1) world)) world)
  else
    world


let rec map_all f width height world =
  if height > 0 then
    map_all f width (height-1) (map_highest_row f width height world)
  else
    world


let world_map f world =
  let width, height, cells = world in
    map_all f width height world


let rec iter_highest_row f width height world =
  ignore (if width > 0 then begin
            f (cell_at (width-1, height-1) world);
            iter_highest_row f (width-1) height world
          end)


let rec iter_all f width height world =
  ignore (if height > 0 then begin
            iter_highest_row f width height world;
            iter_all f width (height-1) world
          end)

let world_iter f world =
  let width, height, cells = world in
    ignore (iter_all f width height world)
