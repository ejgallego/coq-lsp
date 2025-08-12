# coq-lsp WASM prototype for VSCode

We include here a WASM build for the coq-lsp binary,
VSCode-compatible.

- Code derived from jsCoq (c) Shachar Itzhaky
- Note: jsCoq provides an official WASM build for browsers

To build the artifact:

$ tar cvfj ../coq-lsp-wasm.tar.gz --exclude=./node_modules .

