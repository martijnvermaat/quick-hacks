{
  open Parser
  exception Eof
}

rule token = parse
    [' ' '\t']                      { token lexbuf }
  | ['\n' ]                         { EOL }
  | ['0'-'9']+ as d                 { DIGIT(int_of_string d) }
  | 'B'                             { BLANK }
  | ['0'-'0' 'a'-'z' 'A'-'Z']+ as n { NAME(n) }
  | "LEFT"                          { LEFT }
  | "RIGHT"                         { RIGHT }
  | eof                             { raise Eof }
