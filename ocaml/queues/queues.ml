(*
Dit is de implementatie voor een polymorfe
fifo-queue (first-in first-out). 
*)


type 'a queue = 'a list


exception QueueError


let empty = []

let push n q = n::q

let rec pop q = match q with
    []    -> []
  | [_]   -> []
  | n::q' -> n::(pop q')

let rec out q = match q with
    []    -> raise QueueError
  | [n]   -> n
  | _::q' -> out q'
