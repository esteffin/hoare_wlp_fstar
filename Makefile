FSTAR_HOME=..
FSTAR_BIN=fstar.exe
FSTAR=$(FSTAR_HOME)/bin/$(FSTAR_BIN) --fstar_home $(FSTAR_HOME)
STATE=$(FSTAR_HOME)/lib/set.fst $(FSTAR_HOME)/lib/heap.fst stperm.fst

all : hoare_wp

hoare_wp : exp.fst hoare_wp.fst
	$(FSTAR) ../lib/constr.fst exp.fst hoare_wp.fst
