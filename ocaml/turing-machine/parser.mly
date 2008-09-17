%{
open Tape
open Machine
%}
%token <int> DIGIT
%token BLANK
%token <string> NAME
%token LEFT
%token RIGHT
%token EOL
%start main
%type <Machine.rule> main
%%
main:
    expr EOL                { $1 }
;
expr:
    NAME symbol NAME symbol direction { ($1, $2, $3, $4, $5) }
;
symbol:
    DIGIT { Some $1 }
  | BLANK { None }
;
direction:
    LEFT  { Left }
  | RIGHT { Right}
