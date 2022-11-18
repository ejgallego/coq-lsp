## Coq LSP

The `coq-lsp` project aims to provide a lightweight, pure [Language
Server
Protocol](https://microsoft.github.io/language-server-protocol/)
server implementation for the Coq proof assistant, as well as to serve
as a framework for interface experimentation.

**Warning**: This project is at a _early_ stage, and it has **known
bugs**, see the issue tracker for more information. Use at your own
risk. See [install information](#Installation) for install instructions.

Moreover, we expect the code to evolve significantly, contributions
are very welcome, but please **first coordinate** with the dev team
before writing any code.

## Development Channel

Our development channel can be found at [Coq's
Zulip](https://coq.zulipchat.com/#narrow/stream/329642-coq-lsp), don't
hesitate to stop by.

## Features

### Incremental compilation and continuous document checking:

Edit your file, and `coq-lsp` will try to re-check only what is
necessary, continuously. No more dreaded `Ctrl-C Ctrl-N`! Rechecking
tries to be smart, and will ignore whitespace changes.

[insert gif]

In a future release, `coq-lsp` will save its document cache to disk so
you can restart your proof session where you left it at the last time.

Incremental support is undergoing refinement, if `coq-lsp` rechecks
when it should not, please file a bug!

### Smart, Cache-aware Error recovery

`coq-lsp` won't stop checking on errors, but support (and encourages)
working with proof documents that are only partially
working. Moreover, error recovery integrates with the incremental
cache, and will recognize proof structure.

You can edit without fear inside a `Proof. ... Qed.`, the rest of the
document won't be rechecked, unless the proof is completed.

[insert gif]

### Whole-Document Goal Display

Press `Alt+Enter` (or `Cmd+Enter` in Mac) to show goals at point in a side panel.

### Markdown support

Open a markdown file with a `.mv` extension, `coq-lsp` will check the
code parts! `coq-lsp` places human friendly documents at the core of
its design ideas.

[insert gif]

### Document outline:

`coq-lsp` supports document outline, allowing you to jump directly
to definitions in the document.

[insert gif]

### Detailed timing and memory stats

Hover over any Coq sentence, `coq-lsp` will display detailed memory and
timing statistics.

[insert gif]

### Client-side configuration options

`coq-lsp` is configurable, and tries to adapt to your own
workflow. What to do when a proof doesn't check, admit or ignore?  You
decide!

See the `coq-lsp` extension configuration in VSCode for options available.

[insert gif]

### Reusability, standards, modularity

The incremental document checking library of `coq-lsp` has been
designed to be reusable by other projects written in OCaml and with
needs for document validation UI, as well as by other Coq projects
such as jsCoq.

Moreover, we are strongly based on standards, aiming for the least
possible extensions.

## Planned features

### Jump to definition

In progress, pending on https://github.com/coq/coq/pull/16261

### Proof skipping

Configure which proofs to skip or delay, to make your document
workflow more reactive.

### Contextual continuous checking

Check only what is visible, _à la_ Isabelle.

### Server-side Completion Help

### "Semantic" goal and document printing

### LaTeX document support

### Workspace Integration

Don't worry about ever having to build your project again, `coq-lsp`
will detect your workspace and build setup, and will keep everything
up to date automatically.

### Responsible elaboration and refinement

Supporting inlays and Lean-style infoview.

### "Computational", Jupyter-style Documents

### Suggestions / Search panel

## Installation

### Requirements

### Server: opam

TODO

### Server: Building from sources

To build the server, you'll need and environment with the dependencies
stated in `coq-lsp.opam`. [Opam](https://opam.ocaml.org/) users can do
`opam install --deps-only .`.

Once you have done that, do `make`, and the server will be build under
`_build/install/default/bin/`

### Server: Nix development support

There is a Nix flake available which will setup the necessery environment and
can be used via `nix develop`. You can then run `make` as usual.

## Editor support and Client

### Visual Studio Code: Marketplace

TODO

### Visual Studio Code: Building from Sources

Assuming the server is built, install the extension as follows:

 1. Symlink the `editor/code` directory into `~/.vscode/extensions/`.
    ```sh
    ln -s ~/path/to/coq-lsp/editor/code ~/.vscode
    ```
    (link source should be absolute or else it won't work!)
 2. Run `npm install && npm run compile` in `editor/code`.
    ```sh
    (cd editor/code && npm i && npm run compile)
    ```

Now you can launch VS Code through `dune`: `dune exec -- code -n` ,
this will setup the right environment variables such as `PATH` and
`OCAMLPATH`.

Alternatively, you can just install the server and run `code`.

### Emacs

You can use this mode with [eglot]() with `$path_to_server
--std`. Note that `--std` is needed otherwise eglot will choke due to
extra messages.

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
- Shachar Itzhaky (Technion)
- Ramkumar Ramachandra

## Acknowledgments

Work on this server has been made possible thanks to many discussions,
inspirations, and sharing of ideas from colleagues. In particular we'd
like to thank Rudi Grinberg, Andrey Mokhov, Clément Pit-Claudel, and
Makarius Wenzel for their help and advice.
