(*
  Command line program for running soare's turing machines.
*)


let turing program start_state stop_state tape =
  let machine = Machine.create program start_state stop_state tape in
  try
    let before, symbol, after = Machine.tape (Machine.run machine) in
    let filled = List.filter (fun s -> s != None) (symbol :: before @ after) in
    print_int (List.length filled);
    print_newline ()
  with
    | Machine.Deadlock -> print_endline "Reached a deadlock"


let parse_input input =
  let rec convert n =
    if n = 0 then
      [Some 1; None]
    else
      (Some 1)::(convert (n - 1))
  in
  try
    List.concat (List.map convert (List.map int_of_string input))
  with
    | Failure _ -> raise (Failure "Inputs must be natural numbers")


let main () =

  let program_file = ref None
  and input = ref []
  in

  let arguments = Arg.align
    [("-p", Arg.String (fun a -> program_file := Some a),
      " Program (required)")]
  and description = "./soare -p program input_1 ... input_n"
  in

  Arg.parse arguments (fun i -> input := !input @ [i]) description;

  match !program_file, !input with
    | Some program, _ ->
        begin
          try
            turing
              (Util.parse_program program)
              "1"
              "0"
              (parse_input !input)
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
