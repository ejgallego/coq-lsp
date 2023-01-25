COQ_BUILD_CONTEXT=../_build/default/coq

PKG_SET= \
vendor/coq/coq-core.install \
vendor/coq/coq-stdlib.install \
vendor/coq-serapi/coq-serapi.install \
coq-lsp.install

# Get the ocamlformat version from the .ocamlformat file
OCAMLFORMAT=ocamlformat.$$(awk -F = '$$1 == "version" {print $$2}' .ocamlformat)

DUNE=dune
DUNEOPT=--root server

DEV_DEPS= \
dune \
$(OCAMLFORMAT) \
ocaml-lsp-server

.PHONY: build
build: coq_boot
	$(DUNE) build $(DUNEOPT) $(PKG_SET)

.PHONY: check
check: coq_boot
	$(DUNE) build $(DUNEOPT) @check

.PHONY: fmt format
fmt format:
	$(DUNE) fmt $(DUNEOPT)

.PHONY: watch
watch: coq_boot
	$(DUNE) build -w $(DUNEOPT) $(PKG_SET)

.PHONY: build-all
build-all: coq_boot
	$(DUNE) build $(DUNEOPT) @all

server/vendor/coq/config/coq_config.ml:
	cd server/vendor/coq \
	&& ./configure -no-ask -prefix $(shell pwd)/_build/install/default/ \
		-native-compiler no \
	&& cp theories/dune.disabled theories/dune \
	&& cp user-contrib/Ltac2/dune.disabled user-contrib/Ltac2/dune

.PHONY: coq_boot
coq_boot: server/vendor/coq/config/coq_config.ml

.PHONY: clean
clean:
	$(DUNE) clean

# We first pin lablgtk3 as to avoid problems with parallel make
.PHONY: opam
opam:
	opam pin add server/coq-lsp . --kind=path -y
	opam install coq-lsp

# Create local opam switch
.PHONY: opam-switch
opam-switch:
	opam switch create . --empty

# Install opam deps
.PHONY: opam-deps
opam-deps:
	opam install ./server/coq-lsp.opam -y --deps-only

# Install opam deps
.PHONY: opam-dev-deps
opam-dev-deps:
	opam install -y $(DEV_DEPS)

# Initialise submodules
.PHONY: submodules-init
submodules-init:
	git submodule update --init

# Deinitialize submodules
.PHONY: submodules-deinit
submodules-deinit:
	git submodule deinit -f --all

# Build the vscode extension
.PHONY: extension
extension:
	cd editor/code && npm i && npm run vscode:prepublish

# Run prettier
.PHONY: ts-fmt
ts-fmt:
	cd editor/code && npx prettier -w .

.PHONY: make-fmt
make-fmt: build fmt
