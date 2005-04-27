(*
  Automated tests for queue datatype.

  Using the OUnit unit test framework:
  http://www.xs4all.nl/~mmzeeman/ocaml/
*)


open OUnit
open Queues


let test_pop _ =
  assert_equal (pop empty) empty;
  assert_equal (pop (push 1 empty)) empty;
  assert_equal (pop (push 2 (push 1 empty))) (push 2 empty);
  assert_equal (pop (push 3 (push 2 (push 1 empty)))) (push 3 (push 2 empty))


let test_top _ =
  assert_raises QueueError (fun _ -> out empty);
  assert_equal (out (push 1 empty)) 1;
  assert_equal (out (push 2 (push 1 empty))) 1;
  assert_equal (out (push 3 (push 2 (push 1 empty)))) 1


let test_poly _ =
  (*
    Actually, this test is bogus, because the
    Queue implementation wouldn't even compile
    against the interface if it wasn't polymorph.
  *)
  assert_equal (push "a" empty) (push "a" empty);
  assert_equal (push [] empty) (push [] empty)


let test_confusion _ =
  assert_bool "empty queue and queue of 1" (empty <> (push 1 empty));
  assert_bool "queue of 1 and queue of 1,2" ((push 1 empty) <> (push 2 (push 1 empty)))


let test_suite = "queue" >:::
  ["pop"          >:: test_pop;
   "top"          >:: test_top;
   "polymorphism" >:: test_poly;
   "confusion"    >:: test_confusion]


let _ = run_test_tt_main test_suite
