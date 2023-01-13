# Welcome to coq-lsp, a Language Server Protocol-based extension for the Coq Interactive Proof Assistant

`coq-lsp` aims to provide a modern and streamlined experience for
VSCode users, relying on the new [coq-lsp language
server](https://github.com/ejgallego/coq-lsp).

The server provides many nice features such as incremental checking,
advanced error recovery, document information, ... See the server
documentation for more information.

## Features

The `coq-lsp` VSCode extension relies on the standard VSCode LSP
client by Microsoft, with 2 main addons:

- information / goal panel: this will display goals, messages, and
  errors at point. It does also support client-side rendering.  By
  default, Cmd-Enter and mouse click will enable the panel for the
  current point.
- document checking progress, using the right lane decoration.

See the extension configuration options for more information.

## How to install the server:

To install the server please do:

```
opam install coq-lsp
```

The server should also appear in the Coq Platform, and likely by other
channels.

