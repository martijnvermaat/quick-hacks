(* Test our datatype. *)

open Lambda


let _ =


  let id = abs "x" (var "x") in

  let apply_self = abs "x" (app (var "x") (var "x")) in

  let omega = app apply_self apply_self in

  let free_y = var "y" in

  let bound_y = abs "x" (abs "y" (var "x")) in

  let test = app bound_y free_y in

    print_string ("Application of\n  " ^ (term_to_string bound_y) ^ "\non\n  ");
    print_string ((term_to_string free_y) ^ "\nshould yield\n  \\z.y\n");

    print_string "Actual result:\n  ";

    print_string (term_to_string test);
    print_string "\n  ->\n  ";
    print_string (term_to_string (normalize test));
    print_newline ();
