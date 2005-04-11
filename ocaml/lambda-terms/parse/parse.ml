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

  sglri -p lambda.tbl | aterm2xml --implicit | ocaml -I .. xml-light.cma lambda.cma parser.ml

  Unfortunately, sglri from StrategoXT release 0.13 seems to
  suffer from a bug causing it to ignore input from stdin.
*)


exception InvalidParsetree of string


let rec xml_to_lambda = function

    Xml.Element("Lambda", _, Xml.PCData(s)::t::[]) ->
      Lambda.abs s (xml_to_lambda t)

  | Xml.Element("Apply", _, t::u::[]) ->
      Lambda.app (xml_to_lambda t) (xml_to_lambda u)

  | Xml.Element("Var", _, Xml.PCData(s)::[]) ->
      Lambda.var s

  | _ ->
      raise (InvalidParsetree "Not a parse tree of a lambda term")
