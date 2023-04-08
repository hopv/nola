# Compile Coq code
all: Makefile.coq
	@$(MAKE) -f Makefile.coq all
.PHONY: all

# Clean up Coq-generated files and Makefile.coq
clean:
	@$(MAKE) -f Makefile.coq cleanall
	rm -f Makefile.coq Makefile.coq.conf
.PHONY: clean

# Install Coq code
install: Makefile.coq
	@$(MAKE) -f Makefile.coq install
.PHONY: install

# Uninstall Coq code
uninstall: Makefile.coq
	@$(MAKE) -f Makefile.coq uninstall
.PHONY: uninstall

# Generate a Coq document
doc: Makefile.coq
	@$(MAKE) -f Makefile.coq COQDOCEXTRAFLAGS="--no-index --parse-comments" html
.PHONY: doc

# Browse a Coq document
viewdoc: doc
	open ./html/toc.html
.PHONY: viewdoc

# Generate Makefile.coq from _CoqProject
Makefile.coq : _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

# Generate devdep/*-devdep.opam from *.opam,
# clearing build/install/remove entries into []
devdep/%-devdep.opam: %.opam
	@echo "Create devdep for $<"
	@mkdir -p devdep
	@sed -E 's/^(build|install|remove): .*$$/\1: []/' $< > $@

# List devdep/*-devdep.opam files
DEVDEPOPAMS = $(addprefix devdep/, \
	$(addsuffix -devdep.opam, $(basename $(wildcard *.opam))))

# Install devdep/*-devdep.opam
# to fix development dependencies
devdep: $(DEVDEPOPAMS)
	opam install ./devdep
.PHONY: devdep
