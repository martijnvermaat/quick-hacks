(*
  Working with turing machines.
*)


(*
  Print ASCII representation of the machine on stdout.

  TODO: vertical printing
  TODO: graphical printing (e.g. with cairo)
*)
let show machine =
  let state = Machine.state machine
  and (before, symbol, after) = Machine.tape machine
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
  let machine = Machine.create program "1" "0" tape in
  show (Machine.run machine)


(*
  Parse a file containing a list of rules.
*)
let parse_program file =
  let rec parse_rule lexbuf line =
    try
      let rule = ProgramParser.main ProgramLexer.token lexbuf in
      (parse_rule lexbuf (line + 1))@ [rule]
    with
      | Parsing.Parse_error ->
          let e = "Error parsing program `" ^ file ^ "' (line "
            ^ (string_of_int line) ^ ")"
          in
          raise (Failure e)
      | ProgramLexer.Eof ->
          []
    in
  try
    parse_rule (Lexing.from_channel (open_in file)) 1
  with
    | Sys_error e -> raise (Failure ("Error: " ^ e))


(*
  Parse a string of digits and blanks.
*)
let rec parse_tape string =
  try
    let head = match String.sub string 0 1 with
      | " " -> None
      | c   -> Some (int_of_string c)
    and tail = String.sub string 1 ((String.length string) - 1)
    in
    head :: (parse_tape tail)
  with
    | Invalid_argument _ -> []
    | Failure _          ->
        let e = "Only digits and blanks are allowed on the tape" in
        raise (Failure e)


let main () =

  let program_file = ref None
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
