MODS        := Binding Part1A
COQ_SOURCES := $(MODS:%=%.v)

GLOBALS     := .coq_globals

include Makefile.coq

Makefile.coq: Makefile $(COQ_SOURCES)
	coq_makefile $(COQ_SOURCES) \
		COQC = "coqc -dump-glob $(GLOBALS)" \
		>Makefile.coq

.PHONY: doc

doc:
	-mkdir doc
	coqdoc -d doc --glob-from .coq_globals $(COQ_SOURCES)


