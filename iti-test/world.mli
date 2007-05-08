(*
  Interface for the world datatype.

  A world contains cells and reflects a state in Conways Game of Life.
  Some operations on worlds are provided to do calculations on them.
*)


(*
  A cell is a pair stating its state and position in the world.
*)
type state    = Alive | Dead
type position = int * int
type cell     = position * state


(*
  A world hides a number of cells.
*)
type world


(*
  Constructor for a new empty world with no bounds.
*)
val new_world : world


(*
  Calculate changeset for two worlds. This is a list of cells representing
  the difference from world to world'.
*)
val changeset : world -> world -> cell list


(*
  Kill or breed a cell at given position.
*)
val toggle_cell : position -> world -> world


(*
  Play one round of the game and return the update world.
*)
val evolve_world : world -> world
