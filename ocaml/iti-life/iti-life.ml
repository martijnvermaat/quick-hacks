open Graphics

let board_width = 40
let board_height = 40

let field_width = 20
let field_height = 20


let get_state board (x,y) = 
  try
    board.(x).(y);
  with Invalid_argument arg ->
    false

let draw_board board =
  auto_synchronize false;
  for x = 0 to board_width - 1 do
    for y = 0 to board_height - 1 do
      if (get_state !board (x,y)) then set_color red
      else set_color black;
      fill_rect (x * field_width) (y * field_height) field_width field_height
    done
  done;
  auto_synchronize true

let init_board board =
  !board.(28).(30) <- true;
  !board.(29).(30) <- true;
  !board.(29).(31) <- true;
  !board.(30).(31) <- true;
  !board.(30).(32) <- true;
  !board.(31).(32) <- true;
  !board.(31).(33) <- true;
  !board.(32).(33) <- true;;

let b = ref (Array.make_matrix board_width board_height false)

let click board (x, y) =
  ignore (wait_next_event [Button_up]);
  !board.(x / field_width).(y / field_height) <- true;
  draw_board board

let () =
  open_graph (Printf.sprintf " %dx%d" (board_width * field_width) (board_height * field_height));
  init_board b;
  draw_board b;
  try
    while true do
      let st = wait_next_event [Button_down; Key_pressed] in
        if st.button then click b (mouse_pos ());
        if st.keypressed then begin
          let c = st.key in
	        if c = 'q' then raise Exit
        end;
    done
  with 
    | Exit -> exit 0
