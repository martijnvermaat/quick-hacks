(*
Dit is de signatuur voor een polymorf specificatie van  stacks.
Dat wil zeggen dat we in plaats van een element-type "data" gebruik
maken van een type-variabele 'a.
*)


type 'a stack

val  empty : 'a stack
val  push  : 'a -> 'a stack -> 'a stack 

exception Error

val  pop   : 'a stack -> 'a stack 
val  top   : 'a stack -> 'a 
