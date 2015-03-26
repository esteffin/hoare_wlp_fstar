FSTAR_HOME=../pub
FSTAR_BIN=fstar.exe
FSTAR=$(FSTAR_HOME)/bin/$(FSTAR_BIN) --fstar_home $(FSTAR_HOME)

all : hoare_wp

hoare_wp : exp.fst hoare_wp.fst
	$(FSTAR) $(FSTAR_HOME)/lib/constr.fst exp.fst hoare_wp.fst

shallow : shallow.fst
	$(FSTAR) shallow.fst

shallow2 : shallow2.fst
	$(FSTAR) $(FSTAR_HOME)/lib/constr.fst shallow2.fst

deduce0 : deduce1.fst
	$(FSTAR) $(FSTAR_HOME)/lib/list.fst exp.fst deduce0.fst

deduce1 : deduce1.fst
	$(FSTAR) $(FSTAR_HOME)/lib/list.fst deduce1.fst

deduce2 : deduce2.fst
	$(FSTAR) deduce2.fst
