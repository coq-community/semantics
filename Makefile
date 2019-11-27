all: Makefile.coq
	+make -f Makefile.coq all

clean: Makefile.coq
	+make -f Makefile.coq clean
	rm -rf Makefile.coq* interp.ml* _build

Makefile.coq: Make
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

Make: ;

%: Makefile.coq
	+make -f Makefile.coq $@

.PHONY: all clean
