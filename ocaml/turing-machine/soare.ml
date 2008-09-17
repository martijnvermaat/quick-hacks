open Tape
open Machine


let show machine =
  (* todo: print vertical *)
  let state = get_state machine
  and (before, symbol, after) = Machine.get_tape machine
  and print_symbol = function
      None   -> print_string " "
    | Some s -> print_int s
  in
    print_string "s  ";
    List.iter print_symbol before;
    print_symbol symbol;
    List.iter print_symbol after;
    print_endline "";
    print_int state;
    print_string ("  " ^ (String.make (List.length before) ' ') ^ "^");
    print_endline (String.make (List.length after) ' ')


let turing program tape =
  let machine = new_machine program tape in
    show (run machine)


let main () =

  let read_lines file =
    let lines = ref []
    and cin =
      try
        open_in file
      with
          Sys_error e -> raise (Failure ("Error: " ^ e))
    in
    let rec read () =
      try
        lines := !lines @ [input_line cin];
        read ()
      with
          End_of_file -> ()
        | Sys_error e -> raise (Failure ("Error: " ^ e))
    in
      read ();
      !lines

  and parse_program lines =
    let parse line =
      let parse_symbol s =
        if s = " " then
          None
        else
          Some (int_of_string s)
      and parse_direction d =
        match d with
            'r' -> Right
          | 'l' -> Left
          | _   -> raise (Failure "Not a direction")
      in
        (int_of_string (String.sub line 0 1),
         parse_symbol (String.sub line 1 1),
         int_of_string (String.sub line 2 1),
         parse_symbol (String.sub line 3 1),
         parse_direction (String.get line 4))
    in
      try
        List.map parse lines
      with
          Failure e -> raise (Failure ("Error parsing program (" ^ e ^ ")"))

  and parse_input input =
    let rec convert n =
      if n = 0 then
        [Some 1; None]
      else
        (Some 1)::(convert (n - 1))
    in
      List.concat (List.map convert (List.map int_of_string input))

  and program_file = ref None
  and input = ref []
  in
  let arguments = Arg.align [("-p", Arg.String (fun f -> program_file := Some f), " Program")]
  and description = "Run turing machine"
  in

    Arg.parse arguments (fun i -> input := !input @ [i]) description;

    match !program_file with
        Some file ->
          begin
            try
              turing
                (parse_program (read_lines file))
                (parse_input !input)
            with
                Failure e ->
                  print_endline e;
                  exit 1
          end
      | None ->
          print_endline "Required argument `-p' missing";
          Arg.usage arguments description;
          exit 1


(*
  Start main program.
*)
let _ = main ()
