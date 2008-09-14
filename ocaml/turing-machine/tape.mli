type symbol = int option
type direction = Left | Right

type tape

val empty_tape : tape

val load_tape : symbol list -> tape

val do_step : tape -> symbol -> direction -> tape

val current_symbol : tape -> symbol

val get_tape : tape -> (symbol list * symbol * symbol list)
