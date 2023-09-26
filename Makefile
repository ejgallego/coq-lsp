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

test/server/node_modules: test/server/package.json
	cd test/server && npm i

.PHONY: test
test: build test/server/node_modules
	cd test/server && npm test

.PHONY: test-compiler
test-compiler:
	dune runtest

.PHONY: fmt format
fmt format:
	dune fmt $(DUNEOPT)

.PHONY: watch
watch: coq_boot
	dune build -w $(DUNEOPT) $(PKG_SET)

.PHONY: build-all
build-all: coq_boot
	dune build $(DUNEOPT) @all

.PHONY: js
js:
	dune build --profile=release controller-js/coq_lsp_worker.bc.cjs
	cp controller-js/coq_lsp_worker.bc.cjs editor/code/out/coq_lsp_worker.bc.js

# We set -libdir due to a Coq bug on win32, see https://github.com/coq/coq/pull/17289
vendor/coq/config/coq_config.ml:
	cd vendor/coq \
	&& ./configure -no-ask -prefix $(shell pwd)/_build/install/default/ \
	        -libdir $(shell pwd)/_build/install/default/lib/coq \
	        -bytecode-compiler no \
		-native-compiler no \
	&& cp theories/dune.disabled theories/dune \
	&& cp user-contrib/Ltac2/dune.disabled user-contrib/Ltac2/dune

.PHONY: coq_boot
coq_boot: vendor/coq/config/coq_config.ml

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
