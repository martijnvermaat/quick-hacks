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


let _ =

  let x = Xml.parse_string "<a href='url'>TEXT<begin/><end/></a>" in
    Printf.printf "XML formated = \n%s" (Xml.to_string_fmt x);
    print_newline ()
