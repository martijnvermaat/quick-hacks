(*
  Simple unordered binary search trees
*)


(* A tree is a leaf or a node.*)

type 'a tree =
    Node of 'a tree * 'a * 'a tree
  | Leaf


(* Empty tree. *)

let empty = Leaf


(* Insert element. *)
(*
  Note: our tree implements a set, so we do
  not store duplicate entries.
*)

let rec insert e = function
    Leaf ->
      (* Replace leaf with new node. *)
      Node(Leaf, e, Leaf)
  | Node(l, e', r) ->
      if e < e' then
        (* Insert element in left subtree. *)
        Node(insert e l, e', r)
      else if e > e' then
        (* Insert element in right subtree. *)
        Node(l, e', insert e r)
      else
        (* Element is already present (e'). *)
        Node(l, e', r)


(* Check if element is in tree. *)

let rec element_of e = function
    Leaf -> false
  | Node(l, e', r) ->
      if e < e' then element_of e l
      else if e > e' then element_of e r
      else true
