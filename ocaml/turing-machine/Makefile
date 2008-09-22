export OCAMLMAKEFILE = /usr/share/ocamlmakefile/OCamlMakefile

SHARED = tape.mli tape.ml machine.mli machine.ml programParser.mly programLexer.mll util.ml

define PROJ_turing
  SOURCES = $(SHARED) turing.ml
  RESULT = turing
endef
export PROJ_turing

define PROJ_soare
  SOURCES = $(SHARED) soare.ml
  RESULT = soare
endef
export PROJ_soare

ifndef SUBPROJS
  export SUBPROJS = turing soare
endif

all:	bc

%:
	@$(MAKE) -f $(OCAMLMAKEFILE) subprojs SUBTARGET=$@
