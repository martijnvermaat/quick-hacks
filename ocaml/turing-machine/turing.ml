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
    print_string ("s " ^ (String.make " " (String.length state)));
    List.iter print_symbol before;
    print_symbol symbol;
    List.iter print_symbol after;
    print_endline "";
    print_string state;
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

  in
  let rec parse_tape s =
    try
      begin
        match String.sub s 0 1 with
            " " -> None
          | c   -> Some (int_of_string c)
      end :: (parse_tape (String.sub s 1 ((String.length s) - 1)))
    with
        Invalid_argument _ -> []
      | Failure _          -> raise (Failure "Only 0-9 symbols are allowed on the tape")

  and program_file = ref None
  and input = ref None
  in
  let arguments = Arg.align [("-p", Arg.String (fun f -> program_file := Some f), " Program")]
  and description = "./turing -p program tape"
  in

    Arg.parse arguments (fun i -> input := Some i) description;

    match !program_file, !input with
        Some program, Some tape ->
          begin
            try
              turing
                (parse_program (read_lines program))
                (parse_tape tape)
            with
                Failure e ->
                  print_endline e;
                  exit 1
          end
      | None, _ ->
          print_endline "Required argument `-p' missing";
          Arg.usage arguments description;
          exit 1
      | _, None ->
          print_endline "Required tape missing";
          Arg.usage arguments description;
          exit 1


(*
  Start main program.
*)
let _ = main ()
