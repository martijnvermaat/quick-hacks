(*
   Interface for sets as binary search trees
*)


(* Type of tree. *)
type 'a tree


(* Construct trees. *)
val empty : 'a tree
val insert : 'a -> 'a tree -> 'a tree
val remove : 'a -> 'a tree -> 'a tree


(* Element present in tree. *)
val element_of : 'a -> 'a tree -> bool


(* Elements in tree as list. *)
val elements : 'a tree -> 'a list
