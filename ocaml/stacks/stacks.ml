(* Implementatie voor polymorf stacks datatype. *)

type 'a stack = 'a list

exception StackError

let empty = []

let push h s = h::s

let rec pop s = match s with
    []   -> []
  | h::s -> s

let top s = match s with
    []   -> raise StackError
  | h::s -> h
