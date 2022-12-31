Contributing to Coq LSP
=======================

Thank you very much for willing to contribute to coq-lsp!

`coq-lsp` is in alpha stage, the first step for contributing is to get
in touch with the devs at Zulip.

## Compilation

`make` will compile the server, be sure the submodules are properly initialized.

For the client, the recommended setup is `dune exec -- code
editor/code` , that will open the VSCode extension development
environment, you can run the extension from the Run panel.

## Miscellaneous events

- We use `ocamlformat` to automatically format our codebase.
- We use [prettier](https://marketplace.visualstudio.com/items?itemName=esbenp.prettier-vscode) to automatically format files in editor/code.
