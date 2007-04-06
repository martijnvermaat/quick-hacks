open Paperstorage_aux

let () =
  let client = Paperstorage_clnt.PAPERSTORAGE_PROG.PAPERSTORAGE_VERS.create_portmapped_client "priscilla" Rpc.Tcp in
  let _ = Paperstorage_clnt.PAPERSTORAGE_PROG.PAPERSTORAGE_VERS.add_proc client {paper={number=None; author="Martijn"; title="Test paper"; content=Some "inhoud"}} in
    Rpc_client.shut_down client
