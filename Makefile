COQ_BUILD_CONTEXT=../_build/default/coq

PKG_SET= \
vendor/coq/coq-core.install \
vendor/coq/coq-stdlib.install \
vendor/coq-serapi/coq-serapi.install \
coq-lsp.install

# Get the ocamlformat version from the .ocamlformat file
OCAMLFORMAT=ocamlformat.$$(awk -F = '$$1 == "version" {print $$2}' .ocamlformat)

DEV_DEPS= \
dune \
$(OCAMLFORMAT) \
ocaml-lsp-server

.PHONY: build
build: coq_boot
	dune build $(DUNEOPT) $(PKG_SET)

.PHONY: check
check: coq_boot
	dune build $(DUNEOPT) @check

.PHONY: fmt format
fmt format: coq_boot
	dune fmt $(DUNEOPT)

.PHONY: watch
watch: coq_boot
	dune build -w $(DUNEOPT) $(PKG_SET)

.PHONY: build-all
build-all: coq_boot
	dune build $(DUNEOPT) @all

coq/config/coq_config.ml:
	cd vendor/coq \
	&& ./configure -no-ask -prefix $(shell pwd)/_build/install/default/ \
		-native-compiler no
	# && cp theories/dune.disabled theories/dune \
	# && cp user-contrib/Ltac2/dune.disabled user-contrib/Ltac2/dune

.PHONY: coq_boot
coq_boot: coq/config/coq_config.ml

.PHONY: clean
clean:
	dune clean

# We first pin lablgtk3 as to avoid problems with parallel make
.PHONY: opam
opam:
	opam pin add coq-lsp . --kind=path -y
	opam install coq-lsp

# Create local opam switch
.PHONY: opam-switch
opam-switch:
	opam switch create . --empty

# Install opam deps
.PHONY: opam-deps
opam-deps:
	opam install ./coq-lsp.opam -y --deps-only

# Install opam deps
.PHONY: opam-dev-deps
opam-dev-deps:
	opam install -y $(DEV_DEPS)

# Initialise submodules
.PHONY: submodules
submodules-init:
	git submodule update --init
