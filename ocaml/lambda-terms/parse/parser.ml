(*
  Xml-Light:
  http://tech.motion-twin.com/xmllight

  SDF2 grammar:
  Use the Lambda part from the little-lambda
  grammar at
  http://www.cs.uu.nl/~mdejonge/grammar-base/little-lambda.0/index.html

  aterm2xml:
  http://catamaran.labs.cs.uu.nl/twiki/pt/bin/view/Tools/ATermToXml

  SGLR SDF2 parser:
  http://catamaran.labs.cs.uu.nl/twiki/pt/bin/view/Sdf/SdfBundle
*)


(*
  Idea: use SGLR to parse input Lambda term
  with SDF2 Lambda Calculus grammar. Then use
  aterm2xml to transform the resulting aterm
  to XML and parse this with Xml-Light.
*)

(*
  Use like

  sglri -p lambda.tbl -i hoi | aterm2xml --implicit | ocaml xml-light.cma parser.ml

  Unfortunately, sglri seems to suffer from a bug causing
  it to ignore input from stdin.
*)


let _ =

  let x = Xml.parse_in stdin in
    print_string (Xml.to_string_fmt x);
    print_newline ()
