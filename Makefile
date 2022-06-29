.PHONY: coq_boot build build-all clean opam

COQ_BUILD_CONTEXT=../_build/default/coq

build: coq_boot
	dune build $(DUNEOPT) coq/coq-core.install coq/coq-stdlib.install coq-lsp.install

build-all: coq_boot
	dune build $(DUNEOPT) @all

coq/config/coq_config.ml:
	cd coq && ./configure -no-ask -prefix $(shell pwd)/_build/install/default/ -native-compiler no && cp theories/dune.disabled theories/dune

coq_boot: coq/config/coq_config.ml

clean:
	dune clean

# We first pin lablgtk3 as to avoid problems with parallel make
opam:
	opam pin add coq-lsp . --kind=path -y
	opam install coq-lsp
