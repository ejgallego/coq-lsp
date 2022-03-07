.PHONY: default all clean opam

default:
	dune build $(DUNEOPT) coq-lsp.install

all:
	dune build $(DUNEOPT) @all

clean:
	dune clean

# We first pin lablgtk3 as to avoid problems with parallel make
opam:
	opam pin add coq-lsp . --kind=path -y
	opam install coq-lsp

