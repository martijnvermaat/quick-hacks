(*
  Automated tests for naturals datatype.

  Using the OUnit unit test framework:
  http://www.xs4all.nl/~mmzeeman/ocaml/
*)


open OUnit
open Naturals


(*
  [N1] add(x, zero) = x
  [N2] add(x, succ(y)) = succ(add(x, y))
  [N3] mul(x, zero) = zero
  [N4] mul(x, succ(y)) = add(mul(x, y), x)
*)


let test_n1 _ =
  assert_equal (add zero zero) zero;
  assert_equal (add (succ zero) zero) (succ zero);
  assert_equal (add (succ (succ zero)) zero) (succ (succ zero))


let test_n2 _ =
  assert_equal (add zero (succ zero)) (succ (add zero zero));
  assert_equal (add (succ zero) (succ zero)) (succ (add (succ zero) zero));
  assert_equal (add zero (succ (succ zero))) (succ (add zero (succ zero)))


let test_n3 _ =
  assert_equal (mul zero zero) zero;
  assert_equal (mul (succ zero) zero) zero;
  assert_equal (mul (succ (succ zero)) zero) zero


let test_n4 _ =
  assert_equal (mul zero (succ zero)) (add (mul zero zero) zero);
  assert_equal (mul (succ zero) (succ zero)) (add (mul (succ zero) zero) (succ zero));
  assert_equal (mul zero (succ (succ zero))) (add (mul zero (succ zero)) zero)


let test_confusion _ =
  assert_bool "0 ongelijk aan 1" (zero <> (succ zero));
  assert_bool "0 ongelijk aan 2" (zero <> (succ (succ zero)));
  assert_bool "0 ongelijk aan 3" (zero <> (succ (succ (succ zero))));
  assert_bool "1 ongelijk aan 2" ((succ zero) <> (succ (succ zero)));
  assert_bool "1 ongelijk aan 3" ((succ zero) <> (succ (succ (succ zero))))


let test_suite = "naturals" >:::
  ["[N1]"      >:: test_n1;
   "[N2]"      >:: test_n2;
   "[N3]"      >:: test_n3;
   "[N4]"      >:: test_n4;
   "confusion" >:: test_confusion]


let _ = run_test_tt_main test_suite
