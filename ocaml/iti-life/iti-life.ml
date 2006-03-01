open Graphics

let width = 40
let height = 40

let field_width = 20
let field_height = 20

(*
let col = 20
let lig = 10
let pas = 30
*)

let click (x, y) =
  ignore (wait_next_event [Button_up]);
  let fill_field x y =
    fill_rect
      (x * field_width + 1)
      (y * field_width + 1)
      (field_width - 2) 
      (field_height - 2)
  in
    fill_field (x / field_width) (y / field_height)

let draw_grid x y =
  let rec draw_vertical_lines x y =
    if x > 0 then begin
      moveto (x * field_width) (y * field_height);
      lineto (x * field_width) 0;
      draw_vertical_lines (x - 1) y
    end
  in
  let rec draw_horizontal_lines x y =
    if y > 0 then begin
      moveto (x * field_width) (y * field_height);
      lineto 0 (y * field_height);
      draw_horizontal_lines x (y - 1)
    end
  in
    draw_vertical_lines x y;
    draw_horizontal_lines x y

let () =
  open_graph (Printf.sprintf " %dx%d" (width * field_width) (height * field_height));
  set_color black;
  draw_grid width height;
  try
    while true do
      let st = wait_next_event [Button_down; Key_pressed] in
        if st.button then click (mouse_pos ());
        if st.keypressed then begin
          let c = st.key in
	        if c = 'q' then raise Exit
        end;
    done
  with 
    | Exit -> exit 0
