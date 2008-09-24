(*
  Command line program for running turing machines.
*)


let show area machine =

  let before, cell, after = Machine.tape machine in
(*  let cells, size = 10, 50 in
  let width, height = (cells + 1) * size, size * 2 in*)
  let { Gtk.width = width ; Gtk.height = height } = area#misc#allocation in
  let cells = 20 in
  let size = width / cells in
  let ctx = Cairo_lablgtk.create area#misc#window (*Cairo.image_surface_create Cairo.FORMAT_ARGB32 ~width ~height*) in
  (*let ctx = Cairo.create surface in*)

  (* White background *)
  Cairo.set_source_rgb ctx 255. 255. 255. ;
  Cairo.paint ctx ;

  (* Black foreground *)
  Cairo.set_source_rgb ctx 0. 0. 0. ;

  (* Set thickness of brush *)
  (* Cairo.set_line_width ctx 4. ; *)

  (* Draw tape *)
  Cairo.move_to ctx 0. ((float size) /. 4.) ;
  Cairo.rel_line_to ctx (float width) 0. ;
  Cairo.move_to ctx 0. ((float size) *. 1.25) ;
  Cairo.rel_line_to ctx (float width) 0. ;

  (* Draw cell delimiters *)
  Cairo.move_to ctx (0.5 *. (float size)) ((float size) /. 4.) ;
  for i = 0 to cells do
    Cairo.rel_line_to ctx 0. (float size) ;
    Cairo.rel_move_to ctx (float size) (float (-size))
  done;

  (* Apply the ink *)
  Cairo.stroke ctx ;

  (* Draw digits *)
  Cairo.select_font_face ctx "sans" Cairo.FONT_SLANT_NORMAL Cairo.FONT_WEIGHT_NORMAL ;
  Cairo.set_font_size ctx ((float size) /. 2.) ;

  let fe = Cairo.font_extents ctx in

  let num_before = min (List.length before) ((cells - 1) / 2) in
  let num_after = min (List.length after) (cells - ((cells - 1) / 2) - 1) in

  for i = -num_before to num_after do

    let c =
      if i = 0 then cell
      else if i < 0 then List.nth before ((List.length before) + i)
      else List.nth after (i - 1)
    in

    match c with
      | None   -> ()
      | Some n ->

          let s = string_of_int n in

          let te = Cairo.text_extents ctx s in

          Cairo.move_to ctx ((float (((cells - 1) / 2 + 1) * size)) +. (float (i * size)) -. te.Cairo.x_bearing -. te.Cairo.text_width /. 2.)
            (((float size) *. 0.75) -. fe.Cairo.descent +. fe.Cairo.font_height /. 2.) ;
          Cairo.show_text ctx s

  done;

  (* Reading head *)
  Cairo.move_to ctx (float (((cells - 1) / 2 + 1) * size)) ((float size) *. 1.25) ;
  Cairo.line_to ctx ((float ((cells - 1) / 2) +. 0.5) *. (float size)) ((float size) *. 1.75) ;
  Cairo.line_to ctx ((float ((cells - 1) / 2) +. 1.5) *. (float size)) ((float size) *. 1.75) ;
  Cairo.close_path ctx ;
  Cairo.stroke ctx

  (* Output a PNG file *)
  (*Cairo_png.surface_write_to_file surface "triangle.png"*)


let turing program start_state stop_state tape =
  let w = GWindow.window ~title:"Turing Machine" () in
  ignore (w#connect#destroy GMain.quit) ;

  let b = GPack.vbox ~spacing:6 ~border_width:12
    ~packing:w#add () in

  let f = GBin.frame ~shadow_type:`IN
    ~packing:(b#pack ~expand:true ~fill:true) () in

  let area = GMisc.drawing_area
    ~width:800 ~height:200
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
