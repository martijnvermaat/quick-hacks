let show machine =
  (* todo: print vertical *)
  let state = Machine.get_state machine
  and (before, symbol, after) = Machine.get_tape machine
  and print_symbol = function
    | None   -> print_string " "
    | Some s -> print_int s
  in
  print_string ("s " ^ (String.make (String.length state) ' '));
  List.iter print_symbol before;
  print_symbol symbol;
  List.iter print_symbol after;
  print_endline "";
  print_string state;
  print_string ("  " ^ (String.make (List.length before) ' ') ^ "^");
  print_endline (String.make (List.length after) ' ')


let turing program tape =
  let machine = Machine.new_machine program tape in
  show (Machine.run machine)


let main () =

  let parse_program file =
    let rec parse_rule lexbuf =
      try
        (parse_rule lexbuf) @ [(ProgramParser.main ProgramLexer.token lexbuf)]
      with
        | ProgramLexer.Eof -> []
    in
    try
      parse_rule (Lexing.from_channel (open_in file))
    with
      | Sys_error e         -> raise (Failure ("Error: " ^ e))
      | Parsing.Parse_error -> raise (Failure ("Error parsing program `" ^ file ^ "'"))
  in
  let rec parse_tape s =
    try
      begin
        match String.sub s 0 1 with
          | " " -> None
          | c   -> Some (int_of_string c)
      end :: (parse_tape (String.sub s 1 ((String.length s) - 1)))
    with
      | Invalid_argument _ -> []
      | Failure _          -> raise (Failure "Only 0-9 symbols are allowed on the tape")

  and program_file = ref None
  and input = ref None
  in
  let arguments = Arg.align [("-p", Arg.String (fun f -> program_file := Some f), " Program (required)")]
  and description = "./turing -p program tape"
  in

  Arg.parse arguments (fun i -> input := Some i) description;

  match !program_file, !input with
    | Some program, Some tape ->
        begin
          try
            turing
              (parse_program program)
              (parse_tape tape)
          with
            | Failure e ->
                print_endline e;
                exit 1
        end
    | None, _ ->
        Arg.usage arguments description;
        exit 1
    | _, None ->
        Arg.usage arguments description;
        exit 1


(*
  Start main program.
*)
let _ = main ()
