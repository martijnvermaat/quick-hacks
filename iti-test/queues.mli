(*
Dit is de signatuur voor een polymorfe specificatie van een
fifo-queue (first-in first-out). 
*)


type 'a queue

val  empty : 'a queue
val  push   : 'a -> 'a queue -> 'a queue 

exception QueueError

val  pop   : 'a queue -> 'a queue 
val  out    : 'a queue -> 'a 
