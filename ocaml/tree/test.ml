(* Test our datatype. *)

open Tree


(* Test tree by inserting elements of l and then
   removing elements of r. *)

let test_list l r =

  (* Construct tree of given list. *)
  let rec insert_list = function
      []    -> empty
    | x::xs -> insert x (insert_list xs)
  in

  let l = insert_list l in

  (* Construct tree by removing elements of
     given list from l. *)
  let rec remove_list = function
      []    -> l
    | x::xs -> remove x (remove_list xs)
  in

    (* Get tree as list and print elements. *)
    List.iter
      (fun x -> print_int x; print_string "; ")
      (elements (remove_list r));
    print_newline ()


(* Ok do it. *)

let _ =

  test_list [1; 3; 65; 34; 3; 3; 0; 54; 2; 3; 4; 1] [47; 3; 3]
