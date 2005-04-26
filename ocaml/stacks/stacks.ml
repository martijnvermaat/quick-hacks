
type 'a stack = 'a list

let empty : 'a stack  = []
let push  : 'a -> 'a stack -> 'a stack = fun h -> fun s -> h :: s

exception Error

let rec pop (s : 'a stack) =  match s with
                                 [] -> [] 
                               | h :: s ->  s 

let top (s :  'a stack)  =   match s with   
                                 [] -> raise Error 
                               | h :: s ->  h 
