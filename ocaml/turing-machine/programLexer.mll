{
  open ProgramParser
  exception Eof
}

rule token = parse
    [' ' '\t']                        { token lexbuf }
  | ['\n']                            { EOL }
  | ['0'-'9' 'a'-'z' 'A'-'Z']+ as n   { ID(n) }
  | eof                               { raise Eof }
