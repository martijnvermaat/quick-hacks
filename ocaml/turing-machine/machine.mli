type state   = string
type rule    = state * Tape.symbol * state * Tape.symbol * Tape.direction
type machine

exception Converged
exception Deadlock

val create : rule list -> state -> state -> Tape.symbol list -> machine

val step : machine -> machine

val run : machine -> machine

val state : machine -> state

val tape : machine -> (Tape.symbol list * Tape.symbol * Tape.symbol list)
