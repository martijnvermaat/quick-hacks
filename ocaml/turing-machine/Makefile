export OCAMLMAKEFILE = /usr/share/ocamlmakefile/OCamlMakefile

SHARED = tape.mli tape.ml machine.mli machine.ml programParser.mly programLexer.mll util.ml

define PROJ_turing
  SOURCES = $(SHARED) turing.ml
  RESULT = turing
endef
export PROJ_turing

define PROJ_graphical
  SOURCES = $(SHARED) layout.glade graphical.ml
  RESULT = graphical
  INCDIRS = +cairo +lablgtk2
  CLIBS = mlcairo
  OCAMLBLDFLAGS = lablgtk.cma gtkInit.cmo lablglade.cma cairo.cma cairo_lablgtk.cma lablgtksourceview.cma
  OCAMLNLDFLAGS = lablgtk.cmxa gtkInit.cmx lablglade.cmxa cairo.cmxa cairo_lablgtk.cmxa lablgtksourceview.cmxa
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
