## Coq LSP

The `coq-lsp` project aims to provide a lightweight, pure [Language
Server
Protocol](https://microsoft.github.io/language-server-protocol/)
server implementation for the Coq proof assistant, as well as to serve
as a framework for interface experimentation.

**Warning**: This project is at a _very early_ stage, and it has
**known bugs**. Use at your own risk.

Moreover, we expect the code to evolve significantly, including a full
rewrite, so if you would like to contribute, please **first
coordinate** with the dev team before writing any code.

### Development Channel

Our development channel can be found at [Coq's
Zulip](https://coq.zulipchat.com/#narrow/stream/329642-coq-lsp), don't
hesitate to stop by.

## Roadmap

For now the main focus of the project to write clean and maintainable
code, and to provide a smooth user experience.

A core goal at this stage is to provide feedback upstream so the Coq
API can be tailored to provide a good interactive experience.

For the planned first release, we hope to provide a reasonable
implementation of core LSP features, editor support in VS Code.

### Code organization

`coq-lsp` consists of several components:

- `coq-serapi`: [vendored] improved utility functions to handle Coq AST
- `coq`: Utility library / abstracted Coq API. This is the main entry
  point for communication with Coq.
- `fleche`: incremental document processing backend. Exposes a generic
  API, but closely modelled to match LSP methods
- `lsp`: small generic LSP utilities, at some point to be replaced by
  a generic lib
- `controller`: LSP controller, a thin layer translating LSP transport
  layer to `flèche` surface API.

## Features

### Incremental compilation:

Edit your file, and `coq-lsp` will try to re-check only what is necessary.

[insert gif]

Moreover, `coq-lsp` will save its document cache to disk so you can
restart your proof session where you left it at the last time.

This is currently undergoing refinement.

### Document outline:

`coq-lsp` supports LSP document outline, allowing you to jump directly
to definitions.

[insert gif]

### Jump to definition

In progress, pending on https://github.com/coq/coq/pull/16261

## Building the Server

To build the server, you'll need and environment with the dependencies
stated in `coq-lsp.opam`. [Opam](https://opam.ocaml.org/) users can do
`opam install --deps-only .`.

Once you have done that, do `make`, and the server will be build under
`_build/install/default/bin/`

## Editor support and Client

### Visual Studio Code

Assuming the server is built, install the extension as follows:

 1. Symlink the `editor/code` directory into `~/.vscode/extensions/`.
    ```sh
    ln -s ~/path/to/coq-lsp/editor/code ~/.vscode
    ```
    (link source should be absolute or else it won't work!)
 2. Run `npm install` in `editor/code`.
    ```sh
    (cd editor/code && npm i)
    ```

Now you can launch VS Code through `dune`: `dune exec -- code -n` ,
this will setup the right environment variables such as `PATH` and
`OCAMLPATH`.

Alternatively, you can just install the server and run `code`.

### Emacs

You can use this mode with [eglot]() with `$path_to_server
--std`. Note that `--std` is needed otherwise eglot will choke due to
extra messages.

## Licensing information

The license for this project is LGPL 2.1 (or GPL 3+ as stated in the LGPL 2.1).

- This server forked from our previous LSP implementation in for the
  [Lambdapi](https://github.com/Deducteam/lambdapi) by Emilio
  J. Gallego Arias, Frédéric Blanqui, Rodolphe Lepigre, and others.

- Syntax files in editor/code are partially derived from
  [VSCoq](https://github.com/siegebell/vscoq) by Christian J. Bell,
  distributed under the terms of the MIT license (see
  ./vsc-galinas/License-vscoq.text).

## Team

- Ali Caglayan (co-coordinator)
- Emilio J. Gallego Arias (Inria Paris, co-coordinator)
- Ramkumar Ramachandra

## Acknowledgments

Work on this server has been made possible thanks to many discussions,
inspirations, and sharing of ideas from colleagues. In particular we'd
like to thank Rudi Grinberg, Shachar Itzaky, Andrey Mokhov, Clément
Pit-Claudel, and Makarius Wenzel for their help and advice.
