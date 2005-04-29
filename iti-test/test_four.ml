(*
  Automated tests for Four datatype.

  Using the OUnit unit test framework:
  http://www.xs4all.nl/~mmzeeman/ocaml/
*)


open OUnit
open Four


let test_nxt _ =
  assert_equal (nxt (nxt a)) a;
  assert_equal (nxt (nxt b)) b;
  assert_equal (nxt (nxt (nxt a))) (nxt a);
  assert_equal (nxt (nxt (nxt b))) (nxt b);
  assert_equal (nxt (nxt (nxt (nxt a)))) a


let test_confusion _ =
  assert_bool "nxt(a) and a" ((nxt a) <> a);
  assert_bool "nxt(b) and b" ((nxt b) <> b);
  assert_bool "nxt(a) and b" ((nxt a) <> b);
  assert_bool "nxt(b) and a" ((nxt b) <> a)


let test_suite = "four" >:::
  ["nxt(nxt(x))=x" >:: test_nxt;
   "confusion"     >:: test_confusion]


let _ = run_test_tt_main test_suite
