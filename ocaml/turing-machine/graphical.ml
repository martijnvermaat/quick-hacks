(*
  Command line program for running turing machines.
*)


let show machine =

  let before, cell, after = Machine.tape machine in
  let cells, size = 20, 50 in
  let width, height = (cells + 1) * size, size * 2 in
  let surface = Cairo.image_surface_create Cairo.FORMAT_ARGB32 ~width ~height in
  let ctx = Cairo.create surface in

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

  Cairo.move_to ctx 350. ((float size) *. 0.75) ;
  Cairo.show_text ctx "1" ;

  (* Output a PNG file *)
  Cairo_png.surface_write_to_file surface "triangle.png"


let turing program start_state stop_state tape =
  let machine = Machine.create program start_state stop_state tape in
  try
    show (Machine.run machine)
  with
    | Machine.Deadlock -> print_endline "Reached a deadlock"


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
