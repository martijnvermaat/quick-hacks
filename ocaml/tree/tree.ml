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


(* Remove element if present. *)

let rec remove e = function
    Leaf ->
      (* Nothing to remove. *)
      Leaf
  | Node(l, e', r) ->
      if e < e' then
        (* Remove element from left subtree. *)
        Node(remove e l, e', r)
      else if e > e' then
        (* Remove element from right subtree. *)
        Node(l, e', remove e r)
      else
        (* Remove this element. *)
        (* Move right subtree here and move left subtree at
           deepest left of right tree.
           We can take the left tree at once to that location,
           because by definition all elements are smaller then
           the smallest element of the right tree.
        *)
        let rec insert_l = function
            Leaf -> l
          | Node(l', e, r') -> Node(insert_l l', e, r')
        in
          (* Insert l in r. *)
          insert_l r


(* Check if element is in tree. *)

let rec element_of e = function
    Leaf -> false
  | Node(l, e', r) ->
      if e < e' then element_of e l
      else if e > e' then element_of e r
      else true


(* Return elements in tree as list. *)

let rec elements = function
    Leaf -> []
  | Node(l, e, r) ->
      List.append (elements l)
        (List.append [e] (elements r))
