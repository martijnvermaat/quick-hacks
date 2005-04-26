(*
  Automated tests for stack datatype.

  Using the OUnit unit test framework:
  http://www.xs4all.nl/~mmzeeman/ocaml/
*)


open OUnit
open Stacks


(*
  [1] pop(empty) = empty
  [2] top(empty) = error  (-> exception Error)
  [3] pop(push(x,s)) = s
  [4] top(push(x,s)) = x

  Error element hebben we in dit geval
  niet, maar een exception.
*)


let test_pop _ =
  assert_equal (pop empty) empty;
  assert_equal (pop (push 1 empty)) empty;
  assert_equal (pop (push 2 (push 1 empty))) (push 1 empty);
  assert_equal (pop (push 3 (push 2 (push 1 empty)))) (push 2 (push 1 empty))


let test_top _ =
  assert_raises StackError (fun _ -> top empty);
  assert_equal (top (push 1 empty)) 1;
  assert_equal (top (push 2 (push 1 empty))) 2;
  assert_equal (top (push 3 (push 2 (push 1 empty)))) 3


let test_poly _ =
  (*
    Actually, this test is bogus, because the
    Stack implementation wouldn't even compile
    against the interface if it wasn't polymorph.
  *)
  assert_equal (push "a" empty) (push "a" empty);
  assert_equal (push [] empty) (push [] empty)


let test_confusion _ =
  assert_bool "empty stack and non-empty stack" (empty <> (push 1 empty));
  assert_bool "stack of 1 and stack of 1,2" ((push 1 empty) <> (push 2 (push 1 empty)))


let test_suite = "stack" >:::
  ["pop"          >:: test_pop;
   "top"          >:: test_top;
   "polymorphism" >:: test_poly;
   "confusion"    >:: test_confusion]


let _ = run_test_tt_main test_suite
