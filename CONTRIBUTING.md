Contributing to Coq LSP
=======================

Thank you very much for willing to contribute to coq-lsp!

`coq-lsp` has two components:

- a LSP server for Coq project written in OCaml.
- a `coq-lsp` VS Code extension written in TypeScript.

## Compilation

### Server

The server project uses a standard OCaml + dune development setup.

You can use the regular `dune build @check` etc... targets; `coq-lsp`
is released with `dune-release`

`make` will compile the server (the `coq-lsp` binary, to be found in
`_build/install/default/bin/coq-lsp`).

As of today the `main` branch uses some submodules, be sure they are
properly initialized (`make submodules-init`).

We plan to get rid of the submodules soon.

### VS Code Extension

The VS Code extension is setup as a standard npm package using
`esbuild` as the bundler. The extension has a main component and some
webviews components written using React.

For the client, the recommended setup is `dune exec -- code
editor/code` , that will open the VSCode extension development
environment, you can run the extension from the Run panel.

## Miscellaneous events

- We use `ocamlformat` to automatically format our codebase.
- We use
  [prettier](https://marketplace.visualstudio.com/items?itemName=esbenp.prettier-vscode)
  to automatically format files in editor/code.
