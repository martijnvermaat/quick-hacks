open OUnit

let test_empty_list _ =
  assert_equal [1] ([] @ [])

let test_suite = "List testing" >::: ["test_empty_list" >:: test_empty_list]

let _ = run_test_tt_main test_suite
