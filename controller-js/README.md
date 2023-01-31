## coq-lsp Web Worker README

This directory contains the implementation of our LSP-compliant web
worker for Coq / coq-lsp.

As you can see the implementation is minimal, thanks to proper
abstraction of the core of the controller.

For now it is only safe to use the worker in 32bit OCaml mode.

