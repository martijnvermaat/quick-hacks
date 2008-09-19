%{
open Tape
open Machine
%}
%token <string> ID
%token EOL
%start main
%type <Machine.rule> main
%%
main:
  expr EOL { $1 }
;
expr:
  state symbol state symbol direction { ($1, $2, $3, $4, $5) }
;
state:
  ID { $1 }
;
symbol:
  ID {
    if $1 = "B" then
      None
    else
      try
        Some (int_of_string $1)
      with
          Failure _ -> raise Parsing.Parse_error
  }
;
direction:
  ID {
    match $1 with
        "l"     -> Left
      | "r"     -> Right
      | "left"  -> Left
      | "right" -> Right
      | _       -> raise Parsing.Parse_error
  }
