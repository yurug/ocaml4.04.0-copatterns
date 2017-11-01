OCAMLC = ../ocamlc

default: jfla

jfla: jfla.ml
	$(OCAMLC) -custom unix.cma $< -o $@
	./$@

ppdp: ppdp.ml
	$(OCAMLC) -custom unix.cma $< -o $@
	./$@

clean:
	@rm -f jfla{.cmi,.cmo,} ppdp{.cmi,.cmo,} *~
