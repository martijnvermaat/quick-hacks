(* Test our datatype. *)

open Lambda


let _ =


  let id = abs "x" (var "x") in

  let apply_self = abs "x" (app (var "x") (var "x")) in

  let apply_self2 = abs "y" (app (var "y") (var "y")) in

  let omega = app apply_self apply_self in

  let free_y = var "y" in

  let bound_y = abs "x" (abs "y" (var "x")) in

  let test = app bound_y free_y in

    print_string (term_to_string omega);
    print_newline ();
    print_string (debruijn_to_string (debruijnize omega));
    print_newline ();
    print_newline ();

    print_string (term_to_string test);
    print_newline ();
    print_string (debruijn_to_string (debruijnize test));
    print_newline ();
