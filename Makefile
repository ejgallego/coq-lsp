SHELL := /usr/bin/env bash

COQ_BUILD_CONTEXT=../_build/default/coq

PKG_SET= \
vendor/coq/coq-core.install \
vendor/coq/coq-stdlib.install \
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

vendor/coq:
	$(error Submodules not initialized, please do "make submodules-init")

COQVM=yes

# We set -libdir due to a Coq bug on win32, see
# https://github.com/coq/coq/pull/17289 , this can be removed once we
# drop support for Coq 8.16
vendor/coq/config/coq_config.ml: vendor/coq
	EPATH=$(shell pwd) \
	&& cd vendor/coq \
	&& ./configure -no-ask -prefix "$$EPATH/_build/install/default/" \
	        -libdir "$$EPATH/_build/install/default/lib/coq" \
	        -bytecode-compiler $(COQVM) \
		-native-compiler no \
	&& cp theories/dune.disabled theories/dune \
	&& cp user-contrib/Ltac2/dune.disabled user-contrib/Ltac2/dune

# We set windows parameters a bit better, note the need to use forward
# slashed (cygpath -m) due to escaping :( , a conversion to `-w` is
# welcomed if someones has time for this
.PHONY: winconfig
winconfig:
	EPATH=$(shell cygpath -am .) \
	&& cd vendor/coq \
	&& ./configure -no-ask -prefix "$$EPATH\\_build\\install\\default\\" \
	        -libdir "$$EPATH\\_build\\install\\default\\lib\\coq\\" \
		-native-compiler no \
	&& cp theories/dune.disabled theories/dune \
	&& cp user-contrib/Ltac2/dune.disabled user-contrib/Ltac2/dune


.PHONY: js
js: COQVM = no
js: coq_boot
	dune build --profile=release --display=quiet $(PKG_SET) controller-js/coq_lsp_worker.bc.cjs
	mkdir -p editor/code/out/ && cp -a controller-js/coq_lsp_worker.bc.cjs editor/code/out/coq_lsp_worker.bc.js

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
	opam install ./coq-lsp.opam -y --deps-only --with-test

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

# Update submodules from upstream
.PHONY: submodules-update
submodules-update:
	(cd vendor/coq && git checkout master && git pull upstream master)

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

# Helper for users that want a global opam install
.PHONY: opam-update-and-reinstall
opam-update-and-reinstall:
	git pull --recurse-submodules
	for pkg in coq-core coq-stdlib coqide-server coq; do opam install -y vendor/coq/$$pkg.opam; done
	opam install .

.PHONY: patch-for-js
patch-for-js:
	cd vendor/coq && patch -p1 < ../../etc/0001-coq-lsp-patch.patch
	cd vendor/coq && patch -p1 < ../../etc/0001-jscoq-lib-system.ml-de-unix-stat.patch

_LIBROOT=$(shell opam var lib)

# Super-hack
controller-js/coq-fs-core.js: COQVM = no
controller-js/coq-fs-core.js: coq_boot
	dune build --profile=release --display=quiet $(PKG_SET) etc/META.threads
	for i in $$(find _build/install/default/lib/coq-core/plugins -name *.cma); do js_of_ocaml --dynlink $$i; done
	for i in $$(find _build/install/default/lib/coq-lsp/serlib -wholename */*.cma); do js_of_ocaml --dynlink $$i; done
	cd _build/install/default/lib && \
	  js_of_ocaml build-fs -o coq-fs-core.js \
	    $$(find coq-core/ \( -wholename '*/plugins/*/*.js' -or -wholename '*/META' \) -printf "%p:/static/lib/%p ") \
	    $$(find coq-lsp/  \( -wholename '*/serlib/*/*.js'  -or -wholename '*/META' \) -printf "%p:/static/lib/%p ") \
	    ../../../../etc/META.threads:/static/lib/threads/META \
	    $$(find $(_LIBROOT) -wholename '*/str/META'                 -printf "%p:/static/lib/%P ") \
	    $$(find $(_LIBROOT) -wholename '*/seq/META'                 -printf "%p:/static/lib/%P ") \
	    $$(find $(_LIBROOT) -wholename '*/uri/META'                 -printf "%p:/static/lib/%P ") \
	    $$(find $(_LIBROOT) -wholename '*/base/META'                -printf "%p:/static/lib/%P ") \
	    $$(find $(_LIBROOT) -wholename '*/unix/META'                -printf "%p:/static/lib/%P ") \
	    $$(find $(_LIBROOT) -wholename '*/zarith/META'              -printf "%p:/static/lib/%P ") \
	    $$(find $(_LIBROOT) -wholename '*/yojson/META'              -printf "%p:/static/lib/%P ") \
	    $$(find $(_LIBROOT) -wholename '*/findlib/META'             -printf "%p:/static/lib/%P ") \
	    $$(find $(_LIBROOT) -wholename '*/dynlink/META'             -printf "%p:/static/lib/%P ") \
	    $$(find $(_LIBROOT) -wholename '*/parsexp/META'             -printf "%p:/static/lib/%P ") \
	    $$(find $(_LIBROOT) -wholename '*/sexplib/META'             -printf "%p:/static/lib/%P ") \
	    $$(find $(_LIBROOT) -wholename '*/sexplib0/META'            -printf "%p:/static/lib/%P ") \
	    $$(find $(_LIBROOT) -wholename '*/bigarray/META'            -printf "%p:/static/lib/%P ") \
	    $$(find $(_LIBROOT) -wholename '*/cmdliner/META'            -printf "%p:/static/lib/%P ") \
	    $$(find $(_LIBROOT) -wholename '*/ppx_hash/META'            -printf "%p:/static/lib/%P ") \
	    $$(find $(_LIBROOT) -wholename '*/angstrom/META'            -printf "%p:/static/lib/%P ") \
	    $$(find $(_LIBROOT) -wholename '*/stringext/META'           -printf "%p:/static/lib/%P ") \
	    $$(find $(_LIBROOT) -wholename '*/ppx_compare/META'         -printf "%p:/static/lib/%P ") \
	    $$(find $(_LIBROOT) -wholename '*/ppx_deriving/META'        -printf "%p:/static/lib/%P ") \
	    $$(find $(_LIBROOT) -wholename '*/ppx_sexp_conv/META'       -printf "%p:/static/lib/%P ") \
	    $$(find $(_LIBROOT) -wholename '*/memprof-limits/META'      -printf "%p:/static/lib/%P ") \
	    $$(find $(_LIBROOT) -wholename '*/ppx_deriving_yojson/META' -printf "%p:/static/lib/%P ")
	    # These libs are actually linked, so no cma is needed.
	    # $$(find $(_LIBROOT) -wholename '*/zarith/*.cma'         -printf "%p:/static/lib/%P " -or -wholename '*/zarith/META'         -printf "%p:/static/lib/%P ")
	cp _build/install/default/lib/coq-fs-core.js controller-js

# Serlib plugins require:
#   ppx_compare.runtime-lib
#   ppx_deriving.runtime
#   ppx_deriving_yojson.runtime
#   ppx_hash.runtime-lib
#   ppx_sexp_conv.runtime-lib
