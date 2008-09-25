(*
  Command line program for running turing machines.
*)


let show area machine =

  let before, cell, after = Machine.tape machine in

  let cells_left = 1 + List.length before in
  let cells_right = List.length after + 1 in
  let cells = cells_left + 1 + cells_right in

  (* let { Gtk.width = width ; Gtk.height = height } = area#misc#allocation in *)

  let ctx = Cairo_lablgtk.create area#misc#window in

  (* Size of cell *)
  let size = 50. in

  (* We draw the visible cells, with a half blank cell on each side *)
  let tape_top = size /. 4.
  and tape_bottom = size *. 1.25
  and tape_left = size /. 4. in
  let tape_right = size *. (float cells) +. size +. tape_left in

  area#set_size ~width:(int_of_float (tape_right +. size /. 4.)) ~height:(int_of_float (tape_bottom +. size));

  let reading_head = tape_left +. (float (cells_left + 1)) *. size in

  (* White background *)
  Cairo.set_source_rgb ctx 1. 1. 1.;
  Cairo.paint ctx;

  (* Black foreground *)
  Cairo.set_source_rgb ctx 0. 0. 0.;

  (* Set thickness of brush *)
  (* Cairo.set_line_width ctx 4. ; *)

  (* Draw tape *)
  Cairo.move_to ctx tape_left tape_top;
  Cairo.line_to ctx tape_right tape_top;
  Cairo.move_to ctx tape_left tape_bottom;
  Cairo.line_to ctx tape_right tape_bottom;

  (* Draw left cell delimiters *)
  Cairo.move_to ctx (reading_head -. 0.5 *. size) tape_bottom;
  for i = 1 to cells_left do
    Cairo.rel_move_to ctx (-. size) (-. size);
    Cairo.rel_line_to ctx 0. size
  done;

  (* Draw right cell delimiters *)
  Cairo.move_to ctx (reading_head +. 0.5 *. size) tape_bottom;
  for i = 1 to cells_right do
    Cairo.rel_move_to ctx size (-. size);
    Cairo.rel_line_to ctx 0. size
  done;

  (* Draw middle cell delimiters *)
  Cairo.move_to ctx (reading_head -. 0.5 *. size) tape_top;
  Cairo.rel_line_to ctx 0. size;
  Cairo.move_to ctx (reading_head +. 0.5 *. size) tape_top;
  Cairo.rel_line_to ctx 0. size;

  (* Apply the ink *)
  Cairo.stroke ctx ;

  (* Draw digits *)
  Cairo.select_font_face ctx "sans" Cairo.FONT_SLANT_NORMAL Cairo.FONT_WEIGHT_NORMAL ;
  Cairo.set_font_size ctx (size /. 2.) ;

  let fe = Cairo.font_extents ctx in

  (* Draw left digits *)
  for i = 0 to (List.length before - 1) do
    let c = List.nth before (List.length before - 1 - i) in
    match c with
      | None   -> ()
      | Some n ->
          let s = string_of_int n in
          let te = Cairo.text_extents ctx s in
          Cairo.move_to ctx (reading_head -. size *. ((float i) +. 1.) -. te.Cairo.x_bearing -. te.Cairo.text_width /. 2.)
            (((tape_top +. tape_bottom) /. 2.) -. fe.Cairo.descent +. fe.Cairo.font_height /. 2.);
          Cairo.show_text ctx s
  done;

  (* Draw right digits *)
  for i = 0 to (List.length after - 1) do
    let c = List.nth after (List.length after - 1 - i) in
    match c with
      | None   -> ()
      | Some n ->
          let s = string_of_int n in
          let te = Cairo.text_extents ctx s in
          Cairo.move_to ctx (reading_head +. size *. ((float i) +. 1.) -. te.Cairo.x_bearing -. te.Cairo.text_width /. 2.)
            (((tape_top +. tape_bottom) /. 2.) -. fe.Cairo.descent +. fe.Cairo.font_height /. 2.);
          Cairo.show_text ctx s
  done;

  (* Draw center digit *)
  begin match cell with
    | None   -> ()
    | Some n ->
        let s = string_of_int n in
        let te = Cairo.text_extents ctx s in
        Cairo.move_to ctx (reading_head -. te.Cairo.x_bearing -. te.Cairo.text_width /. 2.)
          (((tape_top +. tape_bottom) /. 2.) -. fe.Cairo.descent +. fe.Cairo.font_height /. 2.);
        Cairo.show_text ctx s
  end;

  let pi = 4. *. atan 1. in

  (* Reading head *)
  Cairo.move_to ctx reading_head (tape_bottom +. size /. 8.);
  Cairo.rel_line_to ctx (-. size /. 4.) (size /. 2.);
  Cairo.rel_line_to ctx (size /. 2.) 0.;
  Cairo.close_path ctx;
  Cairo.stroke_preserve ctx;
  Cairo.set_source_rgb ctx 0.5 0.5 0.5;
  Cairo.fill ctx;
  Cairo.set_source_rgb ctx 0. 0. 0.;
  Cairo.arc ctx reading_head (tape_bottom +. size /. 8.) (size /. 8.) 0. (2. *. pi);
  Cairo.fill ctx

  (* Output a PNG file *)
  (*Cairo_png.surface_write_to_file surface "triangle.png"*)


let turing program start_state stop_state tape =
  let w = GWindow.window ~title:"Turing Machine" ~width:500 ~height:200 () in
  ignore (w#connect#destroy GMain.quit) ;

  let scrolled_window = GBin.scrolled_window ~border_width:10
    ~hpolicy:`AUTOMATIC ~vpolicy:`AUTOMATIC ~packing:w#add () in

  let b = GPack.vbox ~spacing:6 ~border_width:12
    ~packing:scrolled_window#add_with_viewport () in

  let f = GBin.frame ~shadow_type:`IN
    ~packing:(b#pack ~expand:true ~fill:true) () in

  let area = GMisc.drawing_area
    (*~width:800 ~height:200*)
    ~packing:f#add () in

  let machine = ref (Machine.create program start_state stop_state tape) in

  let draw area _ = begin
    show area !machine;
    true
  end
  in

  let step area a = begin
    try
      machine := Machine.step !machine
    with
      | Machine.Deadlock -> print_endline "Reached a deadlock"
  end ; draw area a
  in
  ignore (area#event#connect#expose (draw area)) ;
  ignore (w#event#connect#key_press (step area)) ;

  w#show ();
  GMain.Main.main ()


let main () =

  let program_file = ref None
  and start_state = ref None
  and stop_state = ref None
  and input = ref None
  in

  let arguments = Arg.align
    [("-p", Arg.String (fun a -> program_file := Some a),
      " Program (required)");
     ("-i", Arg.String (fun a -> start_state := Some a),
      " Start state (required)");
     ("-s", Arg.String (fun a -> stop_state := Some a),
      " Stop state (required)")]
  and description = "./turing -p program -i start_state -s stop_state tape"
  in

  Arg.parse arguments (fun i -> input := Some i) description;

  match !program_file, !start_state, !stop_state, !input with
    | Some program, Some start, Some stop, Some tape ->
        begin
          try
            turing
              (Util.parse_program program)
              start
              stop
              (Util.parse_tape tape)
          with
            | Failure e ->
                print_endline e;
                exit 1
        end
    | _ ->
        Arg.usage arguments description;
        exit 1


(*
  Start main program.
*)
let _ = main ()
