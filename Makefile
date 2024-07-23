# Makefile for Coq project

# Variables
COQC = coqc
COQFLAGS = -Q . ""

# Dependencies
all: mk_theorems.vo

mk_structure.vo: mk_structure.v
	$(COQC) $(COQFLAGS) mk_structure.v

mk_theorems.vo: mk_structure.vo mk_theorems.v
	$(COQC) $(COQFLAGS) mk_theorems.v

clean:
	rm -f *.vo *.glob