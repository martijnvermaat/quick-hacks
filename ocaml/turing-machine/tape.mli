type symbol    = int option
type direction = Left | Right

type tape

val empty : tape

val create : symbol list -> tape

val step : symbol -> direction -> tape -> tape

val read : tape -> symbol

val contents : tape -> (symbol list * symbol * symbol list)
