(* Test our datatype. *)

open Tree


let _ =


  let set = insert 3 (insert 5 (insert 2 empty)) in

    if element_of 4 set then
      print_string "ja\n"
    else
      print_string "nee\n";

    if element_of 3 set then
      print_string "ja\n"
    else
      print_string "nee\n"
