open Tape
open Machine


let turing program tape =
  let machine = new_machine program tape in
    print_endline "hoi"


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
        else if s = "1" then
          Some 1
        else
          raise (Failure "Only blanks and 1's are supported")
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

  and program_file = ref ""
  and input = ref []
  in

    Arg.parse
      [("-p", Arg.String (fun f -> program_file := f), "Program")]
      (fun i -> input := !input @ [i])
      "Run turing machine";

    try
      turing
        (parse_program (read_lines !program_file))
        (parse_input !input)
    with
        Failure e ->
          print_endline e;
          exit 1


(*
  Start main program.
*)
let _ = main ()
