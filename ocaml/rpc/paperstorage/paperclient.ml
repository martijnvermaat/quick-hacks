open Paperstorage_aux

module CLNT = Paperstorage_clnt.PAPERSTORAGE_PROG.PAPERSTORAGE_VERS


(*
  Create our RPC client.
*)
let create_client hostname =
  try
    CLNT.create_portmapped_client hostname Rpc.Tcp
  with
      Unix.Unix_error (e, _, _) -> failwith (Unix.error_message e)
    | Rpc.Rpc_server e          -> failwith (Printexc.to_string (Rpc.Rpc_server e))


(*
  Add our paper to the server.
*)
let do_add hostname author title filename =

  let paper =
    {paper = {
       number = None;
       author = author;
       title  = title;
       content = Some filename}}
  in

  let client = create_client hostname in    
  let result =
      try
        CLNT.add_proc client paper
      with
          Unix.Unix_error (e, _, _) -> failwith (Unix.error_message e)
        | Rpc.Rpc_server e          -> failwith (Printexc.to_string (Rpc.Rpc_server e))
  in

    Rpc_client.shut_down client;

    match result with
        `status_success {number = Some n} ->
          print_endline ("Added paper " ^ (string_of_int n))
      | `status_success _ -> failwith "Added paper but received no number"
      | `status_failure m -> failwith m


(*
  Retreive paper details from the server.
*)
let do_details hostname number =

  let param =
    let n =
      try
        int_of_string number
      with Failure _ -> failwith ("Not a valid number: " ^ number)
    in
      {number' = n; representation = sparse}
  in

  let client = create_client hostname in    
  let result =
      try
        CLNT.get_proc client param
      with
          Unix.Unix_error (e, _, _) -> failwith (Unix.error_message e)
        | Rpc.Rpc_server e          -> failwith (Printexc.to_string (Rpc.Rpc_server e))
  in

    Rpc_client.shut_down client;

    match result with
        `status_success {author = author; title = title} ->
          print_endline ("Author: " ^ author);
          print_endline ("Title: " ^ title)
      | `status_failure m -> failwith m


(*
  Retreive paper contents from the server.
*)
let do_fetch hostname number =

  let param =
    let n =
      try
        int_of_string number
      with Failure _ -> failwith ("Not a valid number: " ^ number)
    in
      {number' = n; representation = detailed}
  in

  let client = create_client hostname in    
  let result =
      try
        CLNT.get_proc client param
      with
          Unix.Unix_error (e, _, _) -> failwith (Unix.error_message e)
        | Rpc.Rpc_server e          -> failwith (Printexc.to_string (Rpc.Rpc_server e))
  in

    Rpc_client.shut_down client;

    match result with
        `status_success {content = Some s} -> print_string s
      | `status_success _                  -> failwith "Received paper without content"
      | `status_failure m                  -> failwith m


(*
  Retreive paper listing from the server.
*)
let do_list hostname =
  (* TODO *)
  ()


(*
  Read command line arguments and perform the appropriate action.
*)
let paper_client () =

  let usage_error () =
    print_endline "usage: paperclient add <hostname> <author> <title> <filename.{pdf|doc}>";
    print_endline "       paperclient details <hostname> <number>";
    print_endline "       paperclient fetch <hostname> <number>";
    print_endline "       paperclient list <hostname>";
    exit 1
  in

  (if Array.length Sys.argv < 2 then usage_error ());

  match Sys.argv.(1) with
      "add" ->
        (if Array.length Sys.argv < 6 then usage_error ());
        do_add Sys.argv.(2) Sys.argv.(3) Sys.argv.(4) Sys.argv.(5)
    | "details" ->
        (if Array.length Sys.argv < 4 then usage_error ());
        do_details Sys.argv.(2) Sys.argv.(3)
    | "fetch" ->
        (if Array.length Sys.argv < 4 then usage_error ());
        do_fetch Sys.argv.(2) Sys.argv.(3)
    | "list" ->
        (if Array.length Sys.argv < 3 then usage_error ());
        do_list Sys.argv.(2)
    | _     ->
        usage_error ()


(*
  Start main program.
*)
let _ = paper_client ()
