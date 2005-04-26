(*
  Automated tests for naturals datatype.

  Using the OUnit unit test framework:
  http://www.xs4all.nl/~mmzeeman/ocaml/
*)


open OUnit
open Naturals


(*
  [N1] add(x, zero) = x
  [N2] add(x, suc(y)) = suc(add(x, y))
  [N3] mul(x, zero) = zero
  [N4] mul(x, suc(y)) = add(mul(x, y), x)
*)


let test_n1 _ =
  assert_equal (add zero zero) zero;
  assert_equal (add (suc zero) zero) (suc zero);
  assert_equal (add (suc (suc zero)) zero) (suc (suc zero))


let test_n2 _ =
  assert_equal (add zero (suc zero)) (suc (add zero zero));
  assert_equal (add (suc zero) (suc zero)) (suc (add (suc zero) zero));
  assert_equal (add zero (suc (suc zero))) (suc (add zero (suc zero)))


let test_n3 _ =
  assert_equal (mul zero zero) zero;
  assert_equal (mul (suc zero) zero) zero;
  assert_equal (mul (suc (suc zero)) zero) zero


let test_n4 _ =
  assert_equal (mul zero (suc zero)) (add (mul zero zero) zero);
  assert_equal (mul (suc zero) (suc zero)) (add (mul (suc zero) zero) (suc zero));
  assert_equal (mul zero (suc (suc zero))) (add (mul zero (suc zero)) zero)


let test_confusion _ =
  assert_bool "0 ongelijk aan 1" (zero <> (suc zero));
  assert_bool "0 ongelijk aan 2" (zero <> (suc (suc zero)));
  assert_bool "0 ongelijk aan 3" (zero <> (suc (suc (suc zero))));
  assert_bool "1 ongelijk aan 2" ((suc zero) <> (suc (suc zero)));
  assert_bool "1 ongelijk aan 3" ((suc zero) <> (suc (suc (suc zero))))


let test_suite = "naturals" >:::
  ["[N1]"      >:: test_n1;
   "[N2]"      >:: test_n2;
   "[N3]"      >:: test_n3;
   "[N4]"      >:: test_n4;
   "confusion" >:: test_confusion]


let _ = run_test_tt_main test_suite
