let _ =
  try
    let lexbuf = Lexing.from_channel (open_in "test.rules") in
      while true do
        let result = Parser.main Lexer.token lexbuf in
          print_endline "ja!"; flush stdout
      done
  with Lexer.Eof ->
    exit 0
