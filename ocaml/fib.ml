(* Fibonachi *)

let rec fib n =
  if n < 2 then 1
  else fib (n-1) + fib (n-2);;

let main () =
  let _ =
    match (Array.length Sys.argv) with
      0 -> ()
    | 1 -> ()
    | _ ->
        let arg = int_of_string Sys.argv.(1) in
        print_int (fib arg);
        print_newline ();
  in
  print_string "end";
  print_newline ();
  exit 0;;

main ();;
