OCAMLC = /usr/bin/ocamlfind ocamlc
OCAMLOPT = /usr/bin/ocamlfind ocamlopt
OCAMLMKTOP = /usr/bin/ocamlfind ocamlmktop
RPCGEN = /usr/bin/ocamlrpcgen
RPCGEN_FLAGS = -int unboxed

REQUIRES =  unix,equeue,rpc,extlib
RPC_GENERATED = paperstorage_aux.mli paperstorage_aux.ml \
                paperstorage_clnt.mli paperstorage_clnt.ml


all: paperclient papertop


paperclient: paperstorage_aux.cmi paperstorage_aux.cmo \
             paperstorage_clnt.cmi paperstorage_clnt.cmo \
             paperclient.ml
	$(OCAMLC) -o paperclient -package $(REQUIRES) -linkpkg \
              paperstorage_aux.cmo paperstorage_clnt.cmo paperclient.ml

papertop: paperstorage_aux.cmi paperstorage_aux.cmo \
          paperstorage_clnt.cmi paperstorage_clnt.cmo
	$(OCAMLMKTOP) -o papertop -package $(REQUIRES) -linkpkg \
                  paperstorage_aux.cmo paperstorage_clnt.cmo

$(RPC_GENERATED): paperstorage.x
	$(RPCGEN) -aux -clnt $(RPCGEN_FLAGS) paperstorage.x


.SUFFIXES: .cmo .cmi .cmx .ml .mli

.ml.cmo:
	$(OCAMLC) -c -package $(REQUIRES) $<
.mli.cmi:
	$(OCAMLC) -c -package $(REQUIRES) $<
.ml.cmx:
	$(OCAMLOPT) -c -package $(REQUIRES) $<


clean:
	rm -f *~ *.cmi *.cmo *.cmx $(RPC_GENERATED) paperclient papertop
