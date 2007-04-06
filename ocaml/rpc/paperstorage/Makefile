OCAMLC = /usr/bin/ocamlfind ocamlc
OCAMLOPT = /usr/bin/ocamlfind ocamlopt
RPCGEN = /usr/bin/ocamlrpcgen

REQUIRES =  unix,equeue,rpc
RPC_GENERATED = paperstorage_aux.mli paperstorage_aux.ml \
                paperstorage_clnt.mli paperstorage_clnt.ml


all: paperclient


paperclient: paperstorage_aux.cmi paperstorage_aux.cmo \
             paperstorage_clnt.cmi paperstorage_clnt.cmo \
             paperclient.ml
	$(OCAMLC) -o paperclient -package $(REQUIRES) -linkpkg \
              paperstorage_aux.cmo paperstorage_clnt.cmo paperclient.ml

$(RPC_GENERATED): paperstorage.x
	$(RPCGEN) -aux -clnt paperstorage.x


.SUFFIXES: .cmo .cmi .cmx .ml .mli

.ml.cmo:
	$(OCAMLC) -c -package $(REQUIRES) $<
.mli.cmi:
	$(OCAMLC) -c -package $(REQUIRES) $<
.ml.cmx:
	$(OCAMLOPT) -c -package $(REQUIRES) $<


clean:
	rm -f *~ *.cmi *.cmo *.cmx $(RPC_GENERATED) paperclient
