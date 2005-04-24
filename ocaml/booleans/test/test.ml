(*
  Automated tests for booleans datatype.

  Using the OUnit unit test framework:
  http://www.xs4all.nl/~mmzeeman/ocaml/
*)


open OUnit
open Booleans


let test_and _ =
  assert_equal (and' true' true') true';
  assert_equal (and' true' false') false';
  assert_equal (and' false' true') false';
  assert_equal (and' false' false') false'


let test_or _ =
  assert_equal (or' true' true') true';
  assert_equal (or' true' false') true';
  assert_equal (or' false' true') true';
  assert_equal (or' false' false') false'


let test_not _ =
  assert_equal (not' false') true';
  assert_equal (not' true') false'


let test_confusion _ =
  assert_bool "true and false" (true' <> false')


let test_suite = "booleans" >:::
  ["and"       >:: test_and;
   "or"        >:: test_or;
   "not"       >:: test_not;
   "confusion" >:: test_confusion]


let _ = run_test_tt_main test_suite
