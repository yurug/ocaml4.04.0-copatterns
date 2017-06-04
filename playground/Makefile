OCAML = ../ocaml
OCAMLC = ../ocamlc

SRC := $(filter-out paper.ml,$(wildcard *.ml))

default: $(SRC)
	@echo "- Typecheking"
	@for file in $(SRC); do (echo -- $$file; $(OCAML) $$file); done

paper: paper.ml
	$(OCAMLC) -custom unix.cma paper.ml -o paper
	./paper
