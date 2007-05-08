(*
  Automated tests for Game of Life world.

  Using the OUnit unit test framework:
  http://www.xs4all.nl/~mmzeeman/ocaml/
*)


open OUnit
open World


let load_figure =
  List.fold_left (fun w p -> toggle_cell p w) new_world


let compare_lists m a b =
  (*
    This is a dirty hack. We want to assert that the two lists are equal
    modulo their order. This is the case if they are of the same length
    and list a is equal to filtering list a with membership of list b.
    The only assumption needed is that all elements are unique, which they
    are I guess...
  *)
  assert_bool m ((List.length a = List.length b)
                 &&
                 ((List.filter (fun e -> List.mem e b) a) = a))


let assert_evolution initial_figure expected_figure =
  let resulting_cells =
    changeset new_world (evolve_world (load_figure initial_figure))
  and expected_cells =
    changeset new_world (load_figure expected_figure)
  in
    compare_lists "Evolve figure one step" resulting_cells expected_cells


let test_point _ =
  let initial_figure =
    [(0, 0)]
  and expected_figure =
    []
  in
    assert_evolution initial_figure expected_figure


let test_two_points _ =
  let initial_figure =
    [(0, 0); (0, 1)]
  and expected_figure =
    []
  in
    assert_evolution initial_figure expected_figure


let test_block _ =
  let initial_figure =
    [(1, 0); (1, 1);
     (0, 0); (0, 1)]
  and expected_figure =
    [(1, 0); (1, 1);
     (0, 0); (0, 1)]
  in
    assert_evolution initial_figure expected_figure


let test_blinker _ =
  let initial_figure =
    [(0, -1); (0, 0); (0, 1)]
  and expected_figure =
    [( 1, 0);
     ( 0, 0);
     (-1, 0)]
  in
    assert_evolution initial_figure expected_figure


let test_bucket _ =
  let initial_figure =
    [(2, 0);         (2, 2);
     (1, 0); (1, 1); (1, 2)]
  and expected_figure =
    [(2, 0);         (2, 2);
     (1, 0);         (1, 2);
             (0, 1)]
  in
    assert_evolution initial_figure expected_figure


let test_deep_bucket _ =
  let initial_figure =
    [(3, 0);         (3, 2);
     (2, 0);         (2, 2);
     (1, 0); (1, 1); (1, 2)]
  and expected_figure =
    [(2, -1); (2, 0);         (2, 2); (2, 3);
              (1, 0);         (1, 2);
                      (0, 1)]
  in
    assert_evolution initial_figure expected_figure


let test_glider _ =
  let initial_figure =
    [(2, 0); (2, 1); (2, 2);
     (1, 0);
             (0, 1)]
  and expected_figure =
    [        (3, 1);
     (2, 0); (2, 1);
     (1, 0);         (1, 2)]
  in
    assert_evolution initial_figure expected_figure


let test_suite = "world" >:::
  ["two points:\n\n  **\n\nshould disappear"                                              >:: test_two_points;
   "point:\n\n  *\n\nshould disappear"                                                    >:: test_point;
   "block:\n\n  **\n  **\n\nshould stay the same"                                         >:: test_block;
   "blinker:\n\n  ***\n\nshould evolve to\n\n   *\n   *\n   *         "                   >:: test_blinker;
   "bucket:\n\n  * *\n  ***\n\nshould evolve to\n\n  * *\n  * *\n   *"                    >:: test_bucket;
   "deep bucket:\n\n   * *\n   * *\n   ***\n\nshould evolve to\n\n  ** **\n   * *\n    *" >:: test_deep_bucket;
   "glider:\n\n  ***\n  *\n   *\n\nshould evolve to\n\n   *\n  **\n  * *"                 >:: test_glider]


let _ = run_test_tt_main test_suite
