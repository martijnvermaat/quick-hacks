export OCAMLMAKEFILE = OCamlMakefile

SHARED = tape.mli tape.ml machine.mli machine.ml programParser.mly programLexer.mll util.ml

define PROJ_turing
  SOURCES = $(SHARED) turing.ml
  RESULT = turing
endef
export PROJ_turing

define PROJ_graphical
  SOURCES = $(SHARED) graphical.ml
  RESULT = graphical
  INCDIRS = /home/mvt600/public/usr/lib/ocaml/3.09.2/cairo
  OCAMLBLDFLAGS = cairo.cma
  OCAMLNLDFLAGS = cairo.cmxa
endef
export PROJ_graphical

define PROJ_soare
  SOURCES = $(SHARED) soare.ml
  RESULT = soare
endef
export PROJ_soare

ifndef SUBPROJS
  export SUBPROJS = turing graphical soare
endif

all:	bc

%:
	@$(MAKE) -f $(OCAMLMAKEFILE) subprojs SUBTARGET=$@
