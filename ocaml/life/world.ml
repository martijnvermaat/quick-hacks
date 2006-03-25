type state = Living | Dead
type coordinate = int * int
type cell = state * coordinate

(* internal representation *)
(* a world is conceptually unbounded *)
(* not any more, width,height is included *)
type world = int * int * coordinate list

let new_world width height = width, height, []

let rec remove_from_list pos = function
    []   -> []
  | h::t -> if h = pos then t else h::(remove_from_list pos t)

(* this should not be used, do away with it *)
let cell_at pos world =
  let width, height, cells = world in
    if List.mem pos cells then
      Living, pos
    else
      Dead, pos


let toggle_cell pos world =
  let width, height, cells = world in
    if List.mem pos cells then
      width, height, remove_from_list pos cells
    else
      width, height, pos::cells


let add_cell cell world =
  let s, pos = cell in
  let width, height, cells = world in
  let cell_removed = remove_from_list pos cells in
    match s with
        Living -> width, height, pos::cell_removed
      | _      -> width, height, cell_removed


let neighbours pos world =
  let x, y = pos in
  let list_of_neighbours =
    cell_at (x, y+1) world
    :: cell_at (x+1, y+1) world
    :: cell_at (x+1, y) world
    :: cell_at (x+1, y-1) world
    :: cell_at (x, y-1) world
    :: cell_at (x-1, y-1) world
    :: cell_at (x-1, y) world
    :: cell_at (x-1, y+1) world
    :: []
  in
    List.fold_left
      (fun n -> function
           (Living, _) -> n + 1
         | _           -> n)  (* isn't there an identity function? *)
      0
      list_of_neighbours


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




(*
  Idea:
  have an *abstract* datatype for the board implemented
  as a list of coordinates for living cells.
  operations on the board return cells as cell datatype,
  a tuple of coordinates and state.
  for the next round a new board is created.
  maybe have coordinates (0,0) in the center of the board,
  to make encoding of interesting figures easy.

  performance is reasonable but not good. idea for
  optimization is to only evolve cells that have potential
  to be alive (living cells and their neighbours).

  idea stolen from
  http://homepages.inf.ed.ac.uk/dts/fps/pract3-2004/pract3.sml
*)
