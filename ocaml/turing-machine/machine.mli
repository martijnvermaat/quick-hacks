open Tape

type state = int
type rule = state * symbol * state * symbol * direction
type machine

val do_step' : machine -> machine

val run : machine -> machine

val new_machine : rule list -> symbol list -> machine

val get_state : machine -> state

val get_tape : machine -> (symbol list * symbol * symbol list)
