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

    if alpha_convertible omega (app apply_self apply_self2) then
      print_string "Ja!!!\n"
    else
      print_string "Nee!!!\n"
