(* Test our datatype and parser. *)


(*
  sglri -p parse/lambda.tbl | aterm2xml --implicit | \
    ocaml -I parse lambda.cmo xml-light.cma parse.cmo test.ml
*)


let _ =

  let xml = Xml.parse_in stdin in

  let term = Parse.xml_to_lambda xml in

  let debruijn = Lambda.debruijnize term in

    print_string "Term: ";
    print_string (Lambda.term_to_string term);
    print_newline ();

    print_string "DeBruijn: ";
    print_string (Lambda.debruijn_to_string debruijn);
    print_newline ();

    print_string "Normal form: ";
    print_string (Lambda.term_to_string
                    (Lambda.normalize term));
    print_newline ()
