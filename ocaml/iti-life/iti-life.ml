open Graphics

let board_width = 80
let board_height = 80

let field_width = 10
let field_height = 10


let get_state board (x,y) = 
  try
    let state (s, _) = s in
      state !board.(x).(y)
  with Invalid_argument arg ->
    false

let get_neighbours board (x,y) = 
  try
    let neighbours (_, n) = n in
      neighbours !board.(x).(y)
  with Invalid_argument arg ->
    0

let draw_board board =
  auto_synchronize false;
  for x = 0 to board_width - 1 do
    for y = 0 to board_height - 1 do
      if (get_state board (x,y)) then set_color red
      else set_color black;
      fill_rect (x * field_width) (y * field_height) field_width field_height
    done
  done;
  auto_synchronize true

let calculate_neighbours board =
  for x = 0 to board_width - 1 do
    for y = 0 to board_height - 1 do
      let int_of_state pos = if get_state board pos then 1 else 0 in
      let s = get_state board (x, y) in
      let n =
	    int_of_state (x-1,y+1) + int_of_state (x,y+1) + int_of_state (x+1,y+1) +
	      int_of_state (x-1,y) +
	      int_of_state (x+1,y) +
	      int_of_state (x-1,y-1) + int_of_state (x,y-1) + int_of_state (x+1,y-1) in
        !board.(x).(y) <- (s, n)
    done
  done

let evolve_cell board pos =
  let state = get_state board pos 
  and neighbours = get_neighbours board pos in
    match neighbours with
      | 2 -> if state = true then true else false
      | 3 -> if state = false then true else true
      | _ -> false

let evolve_board board =
  calculate_neighbours board;
  for x = 0 to board_width - 1 do
    for y = 0 to board_height - 1 do
      !board.(x).(y) <- (evolve_cell board (x,y), 0)
    done
  done

(*
let init_board board =
  !board.(28).(30) <- (true, 0);
  !board.(29).(30) <- (true, 0);
  !board.(29).(31) <- (true, 0);
  !board.(30).(31) <- (true, 0);
  !board.(30).(32) <- (true, 0);
  !board.(31).(32) <- (true, 0);
  !board.(31).(33) <- (true, 0);
  !board.(32).(33) <- (true, 0)
*)

let b = ref (Array.make_matrix board_width board_height (false, 0))

let click board (x, y) =
  ignore (wait_next_event [Button_up]);
  !board.(x / field_width).(y / field_height) <- (true, 0);
  draw_board board

let () =
  open_graph (Printf.sprintf " %dx%d" (board_width * field_width) (board_height * field_height));
  (* init_board b; *)
  draw_board b;
  try
    while true do
      let st = wait_next_event [Button_down; Key_pressed] in
        if st.button then click b (mouse_pos ());
        if st.keypressed then begin
          let c = st.key in
	        if c = 'q' then raise Exit
            else if c = 'n' then begin
              evolve_board b;
              draw_board b
            end
        end
    done
  with
    | Exit -> exit 0
