(* Test our datatype. *)


let _ =


  let id = Lambda.Abs("x", Lambda.Var("x")) in

  let apply_self = Lambda.Abs("x",
                              Lambda.App(Lambda.Var("x"),
                                         Lambda.Var("x"))) in

  let omega = Lambda.App(apply_self, apply_self) in

  let free_y = Lambda.Var("y") in

  let bound_y = Lambda.Abs("x", Lambda.Abs("y", Lambda.Var("x"))) in

  let test = (Lambda.App(bound_y, free_y)) in

    print_string ("Application of\n  " ^ (Lambda.show bound_y) ^ "\non\n  ");
    print_string ((Lambda.show free_y) ^ "\nshould yield\n  \\z.y\n");

    print_string "Actual result:\n  ";

    print_string (Lambda.show test);
    print_string "\n  ->\n  ";
    print_string (Lambda.show (Lambda.normalize test));
    print_newline ();
