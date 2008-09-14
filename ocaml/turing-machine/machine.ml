open Tape

type state = int
type rule = state * symbol * state * symbol * direction
type machine = rule list * state * tape

let do_step' machine =
  let (rules, state, tape) = machine in
  let (_, _, s, c, d) = List.find (fun (s, c, _, _, _) -> s = state && c = (current_symbol tape)) rules in
    rules, s, (do_step tape c d)

let new_machine rules input =
  rules, 1, (load_tape input)
