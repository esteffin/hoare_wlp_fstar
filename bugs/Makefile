FSTAR_HOME=../../pub
FSTAR_BIN=fstar.exe
FSTAR=$(FSTAR_HOME)/bin/$(FSTAR_BIN) --fstar_home $(FSTAR_HOME) --trace_error
STATE=$(FSTAR_HOME)/lib/set.fst $(FSTAR_HOME)/lib/heap.fst stperm.fst

all : bug_1 bug_2 bug_3 bug_4

# Fixed on trunk already
bug_1 : exp.fst bug_1.fst
	$(FSTAR) $(FSTAR_HOME)/lib/constr.fst exp.fst bug_1.fst

bug_2 : exp.fst bug_2.fst
	$(FSTAR) bug_2.fst

bug_3 : exp.fst bug_3.fst
	$(FSTAR) $(FSTAR_HOME)/lib/constr.fst exp.fst bug_3.fst

bug_5 : exp.fst bug_5.fst
	$(FSTAR) $(FSTAR_HOME)/lib/constr.fst exp.fst bug_5.fst

bug_5b : exp.fst bug_5b.fst
	$(FSTAR) $(FSTAR_HOME)/lib/constr.fst exp.fst bug_5b.fst

bug_6 : bug_6.fst
	$(FSTAR) bug_6.fst

bug_7 : bug_7.fst
	$(FSTAR) bug_7.fst

# CH: This gave Enrico a segmentation fault; I cannot reproduce it though
bug_8 : bug_8.fst
	$(FSTAR) bug_8.fst
