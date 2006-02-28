open Graphics

let width = 1000
let height = 800

(*
let col = 20
let lig = 10
let pas = 30
*)

let () =
  open_graph (Printf.sprintf " %dx%d" width height);
  set_color black

let click (x,y) =
  ignore (wait_next_event [Button_up]);
  moveto x y;
    draw_char (Char.chr (Char.code '0' + 59))

let () = 
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
