open Graphics

let board_width = 80
let board_height = 80

let field_width = 10
let field_height = 10


type cell = Living | Dead
type coordinate = int * int
(* a cell consists of an (x,y) position and a state (include coordinate?) *)
(* type cell = coordinate * state *)
(* board contains coordinates of living cells (include width,height?) *)
type board = coordinate list

let empty_board = []

let rec remove_from_list pos = function
    []   -> []
  | h::t -> if h = pos then t else h::(remove_from_list pos t)

let cell_at pos board =
  if List.mem pos board then
    Living
  else
    Dead

let toggle_cell pos board =
  match cell_at pos board with
      Living -> remove_from_list pos board
    | Dead   -> pos::board


(*
  Idea:
  have an *abstract* datatype for the board implemented
  as a list of coordinates for living cells.
  operations on the board return cells as cell datatype,
  a tuple of coordinates and state.
  for the next round a new board is created.
  maybe have coordinates (0,0) in the center of the board,
  to make encoding of interesting figures easy.

  idea stolen from
  http://homepages.inf.ed.ac.uk/dts/fps/pract3-2004/pract3.sml
*)


let draw_board b =
  auto_synchronize false;
  for x = 0 to board_width - 1 do
    for y = 0 to board_height - 1 do
      begin
        match cell_at (x, y) b with
            Living -> set_color red
          | Dead   -> set_color black
      end;
      fill_rect (x * field_width) (y * field_height) field_width field_height
    done
  done;
  auto_synchronize true;
  b

let click board (x, y) =
  ignore (wait_next_event [Button_up]);
  let pos = x/field_width, y/field_height in
    draw_board (toggle_cell pos board)

let evolve_board board =
  board

let rec main board =
  let new_board =
    begin
      let st = wait_next_event [Button_down; Key_pressed] in
        if st.button then
          click board (mouse_pos ())
        else if st.keypressed then
          match st.key with
              'q' -> raise Exit
            | ' ' -> evolve_board board
            | _   -> board
        else
          board
    end
  in
    main new_board


let () =
  open_graph (Printf.sprintf " %dx%d" (board_width * field_width) (board_height * field_height));
  try
    main empty_board
  with
    | Exit -> exit 0
