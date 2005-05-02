(*
  Automated tests for Four datatype.

  Using the OUnit unit test framework:
  http://www.xs4all.nl/~mmzeeman/ocaml/
*)


open OUnit
open Four


let test_nxt _ =
  assert_bool "nxt(nxt(a))=a" ((nxt (nxt a)) = a);
  assert_bool "nxt(nxt(b))=b" ((nxt (nxt b)) = b);
  assert_bool "nxt(nxt(nxt(a)))=nxt(a)" ((nxt (nxt (nxt a))) = (nxt a));
  assert_bool "nxt(nxt(nxt(b)))=nxt(b)" ((nxt (nxt (nxt b))) = (nxt b));
  assert_bool "nxt(nxt(nxt(nxt(a))))=a" ((nxt (nxt (nxt (nxt a)))) = a);
  assert_bool "nxt(nxt(nxt(nxt(b))))=b" ((nxt (nxt (nxt (nxt b)))) = b)


let test_confusion _ =
  assert_bool "a and b" (a <> b);
  assert_bool "nxt(a) and a" ((nxt a) <> a);
  assert_bool "nxt(b) and b" ((nxt b) <> b);
  assert_bool "nxt(a) and b" ((nxt a) <> b);
  assert_bool "nxt(b) and a" ((nxt b) <> a);
  assert_bool "nxt(nxt(a)) and b" ((nxt (nxt a)) <> b);
  assert_bool "nxt(nxt(b)) and a" ((nxt(nxt b)) <> a)


let test_suite = "four" >:::
  ["nxt(nxt(x))=x" >:: test_nxt;
   "confusion"     >:: test_confusion]


let _ = run_test_tt_main test_suite
