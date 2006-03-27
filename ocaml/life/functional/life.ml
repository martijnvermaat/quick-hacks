(*
  Game of Live implementation in OCaml

  March 2006, Martijn Vermaat

  Ideas/todo:
  * automatic constant evolving.
  * storing and loading of figures.
  * have position (0,0) in center for easier storing of figures.
  * connect left/right and top/bottom edges of world.
  * the calculated world is potentially infinite in size, with a smarter
    interface we could do nice things here (zooming, traveling, etc).
    at the moment we do not use computations outside the bourd that have no
    effect on the board.
  * don't draw cells outside the visible board.
*)


open Graphics
open World


(*
  Configuration.
  A board of 50x50 is reasonable, with fields 10x10.
*)
let board_width, board_height = 50, 50
and field_width, field_height = 10, 10
and dead_color                = black
and living_color              = blue


(*
  Redraw all cells in given changeset on the board. Use double buffering to
  prevent the board from flickering (turn of graphics auto synchronization).
  todo: only draw cells that are inside the board
*)
let draw_changeset changeset =
  let fill_cell (x, y) color =
    set_color color;
    let x' = x * field_width and y' = y * field_height in
      fill_rect x' y' (field_width - 1) (field_height - 1)
  in
  let draw_cell = function
      Living, pos -> fill_cell pos living_color
    | Dead, pos   -> fill_cell pos dead_color
  in
    auto_synchronize false;
    List.iter draw_cell changeset;
    auto_synchronize true


(*
  Toggle state of the cell that we clicked and return the updated world.
*)
let click (x, y) world =
  ignore (wait_next_event [Button_up]);
  let pos = x/field_width, y/field_height in
    toggle_cell pos world


(*
  Load some stored figure in the world. Work this out sometime for more
  functionality.
*)
let load_figure world =
  let glider  = [(20,20);(21,20);(22,20);(20,21);(21,22)]
  and block   = [(20,20);(21,20);(21,21);(20,21)]
  and boat    = [(20,20);(21,20);(21,21);(19,21);(20,22)]
  and blinker = [(20,20);(20,21);(20,22)]
  in
  let figure = List.map (fun pos -> (Living, pos)) glider
  in
    load_cells figure world


(*
  Main loop takes a world and waits for the user to do something. This can be
  a request to play a round of the game, update the state of a cell, etc. This
  is repeated with the possibly updated world.
  This function is tail-recursive so it should not perform worse than an
  imperative 'while true' loop.
  Exit is raised if the user wants to quit the game.
*)
let rec main world =
  let st = wait_next_event [Button_down; Key_pressed] in
  let next_world =
    begin
      if st.button then
        click (mouse_pos ()) world
      else if st.keypressed then
        match st.key with
            'q' -> raise Exit
          | 'l' -> load_figure world
          | ' ' -> evolve_world world
          | _   -> world
      else
        world
    end
  in
    draw_changeset (changeset world next_world);
    main next_world


(*
  Start by creating a new window for the board and call the main loop with an
  empty world.
*)
let () =
  open_graph (Printf.sprintf " %dx%d"
                (board_width * field_width)
                (board_height * field_height));
  set_window_title "Game of Life";
  set_color dead_color;
  fill_rect 0 0 (board_width * field_width) (board_height * field_height);
  try
    main new_world
  with
      Exit              -> exit 0
    | Graphic_failure _ -> exit 0   (* raised when closing the window *)
