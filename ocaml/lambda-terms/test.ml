(* Test our datatype. *)


(* Omega term. *)

let _ =

  let omega = Lambda.Application(
    Lambda.Abstraction("x", Lambda.Application(Lambda.Var("x"), Lambda.Var("x"))),
    Lambda.Abstraction("x", Lambda.Application(Lambda.Var("x"), Lambda.Var("x"))))
  in

  print_string "Should print (\\x.x x)(\\x.x x):\n";
  print_string (Lambda.show omega);
  print_newline ();

  print_string "Should print true:\n";
  print_string (string_of_bool (Lambda.isredex omega));
  print_newline ();
