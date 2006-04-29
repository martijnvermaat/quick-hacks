(*
  Automated tests for Toy datatype.

  Using the OUnit unit test framework:
  http://www.xs4all.nl/~mmzeeman/ocaml/
*)


open OUnit
open Toy


let test_t1 _ =
  assert_bool "nxt(nxt(c))=d" ((nxt (nxt c)) = d)


let test_t2 _ =
  assert_bool "nxt(nxt(nxt(c)))=c" ((nxt (nxt (nxt c))) = c);
  assert_bool "nxt(nxt(nxt(d)))=d" ((nxt (nxt (nxt d))) = d);
  assert_bool "nxt(nxt(nxt(nxt(c))))=nxt(c)" ((nxt (nxt (nxt (nxt c)))) = (nxt c));
  assert_bool "nxt(nxt(nxt(nxt(d))))=nxt(d)" ((nxt (nxt (nxt (nxt d)))) = (nxt d));
  assert_bool "nxt(nxt(nxt(nxt(nxt(d)))))=nxt(nxt(d))" ((nxt (nxt (nxt (nxt (nxt d))))) = (nxt (nxt d)))


let test_confusion _ =
  assert_bool "c and d" (c <> d);
  assert_bool "nxt(c) and c" ((nxt c) <> c);
  assert_bool "nxt(d) and d" ((nxt d) <> d);
  assert_bool "nxt(c) and d" ((nxt c) <> d);
  assert_bool "nxt(nxt(d)) and c" ((nxt (nxt c)) <> d)


let test_suite = "toy" >:::
  ["nxt(nxt(c))=d"      >:: test_t1;
   "nxt(nxt(nxt(x)))=x" >:: test_t2;
   "confusion"          >:: test_confusion]


let _ = run_test_tt_main test_suite
