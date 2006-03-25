open Graphics
open World

let board_width = 50
let board_height = 50

let field_width = 10
let field_height = 10


let draw_board world =
  auto_synchronize false;
  for x = 0 to board_width - 1 do
    for y = 0 to board_height - 1 do
      begin
        match cell_at (x, y) world with
            Living, _ -> set_color red
          | Dead, _   -> set_color black
      end;
      fill_rect (x * field_width) (y * field_height) field_width field_height
    done
  done;
  auto_synchronize true;
  world

let click world (x, y) =
  ignore (wait_next_event [Button_up]);
  let pos = x/field_width, y/field_height in
    toggle_cell pos world

let evolve_state state neighbours =
  (* this can be nicer *)
  match state, neighbours with
      _, 3      -> Living
    | Living, 2 -> Living
    | _         -> Dead

let evolve_world world =
  (*
    problem is that world does has no explicit bounds. a map over this world
    is conceptually fine, but not straightforward to implement
    solution 1) add width,height to world
                + simple
                - ugly
    solution 2) let it just calculate as far as it wants to, but only use
                what's inside the board dimensions
                + simple?
                - after many rounds there can be many unused cells
    solution 3) a lazy version of solution 2
                + elegant
                - hard?
  *)
  world_map (function s, pos -> evolve_state s (neighbours pos world), pos) world

let rec main world =
  let next_world =
    begin
      let st = wait_next_event [Button_down; Key_pressed] in
        if st.button then
          draw_board (click world (mouse_pos ()))
        else if st.keypressed then
          match st.key with
              'q' -> raise Exit
            | ' ' -> draw_board (evolve_world world)
            | _   -> world
        else
          world
    end
  in
    main next_world


let () =
  open_graph (Printf.sprintf " %dx%d" (board_width * field_width) (board_height * field_height));
  try
    main (new_world board_width board_height)
  with
    | Exit -> exit 0
