FSTAR_HOME=..
FSTAR_BIN=fstar
FSTAR=$(FSTAR_HOME)/bin/$(FSTAR_BIN) --fstar_home $(FSTAR_HOME)
STATE=$(FSTAR_HOME)/lib/set.fst $(FSTAR_HOME)/lib/heap.fst stperm.fst

all : wp

wp : exp.fst wp.fst
	$(FSTAR) exp.fst wp.fst
