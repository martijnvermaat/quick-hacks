(*
Dit is de signatuur voor een polymorf specificatie van  stacks.
Dat wil zeggen dat we in plaats van een element-type "data" gebruik
maken van een type-variabele 'a.
*)


type 'a stack

val  empty : 'a stack
val  push  : 'a -> 'a stack -> 'a stack 

(*
  Om zo veel mogelijk overeen te komen met
  de stack-of-data uit het eqlog deel, geeft
  pop op de lege stack de lege stack terug
  en top een error (we kunnen niet een
  speciaal 'error' element hebben van type 'a).
*)

exception Error

val  pop   : 'a stack -> 'a stack 
val  top   : 'a stack -> 'a 
