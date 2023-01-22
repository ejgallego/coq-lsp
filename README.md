## Coq LSP

`coq-lsp` is a [Language
Server](https://microsoft.github.io/language-server-protocol/) and [Visual
Studio Code](https://code.visualstudio.com/) extension for the [Coq Proof
Assistant](https://coq.inria.fr).

Key [features](#Features) of `coq-lsp` are continuous and incremental document
checking, advanced error recovery, markdown support, positional goals and
information panel, performance data, and more.

`coq-lsp` aims to provide a seamless, modern interactive theorem proving
experience, as well as to serve as a platform for research and UI integration
with other projects.

### Installation

In order to use `coq-lsp` you'll need to install [**both**](etc/FAQ.md) the
`coq-lsp` server, and the Visual Studio Code extension:

#### Server

- **opam**: `opam install coq-lsp`
- **Nix** (coming soon)
- **Coq Platform** (coming soon)
- [Do it yourself!](#server-1)

#### **Visual Studio Code**:
- Official Marketplace: https://marketplace.visualstudio.com/items?itemName=ejgallego.coq-lsp
- Open VSX: https://open-vsx.org/extension/ejgallego/coq-lsp

### FAQ

See our [list of frequently-asked questions](./etc/FAQ.md).

### Contributing

Contributions are very welcome! Feel free to chat with the dev team in Zulip, or
just use the standard GitHub facilities. We will soon publish a thing of
interesting projects for `coq-lsp` in case you are looking for ideas.

### Development Channel

`coq-lsp` development channel it at [Coq's
Zulip](https://coq.zulipchat.com/#narrow/stream/329642-coq-lsp), don't hesitate
to stop by.

### Troubleshooting

- Most problems can be resolved by restarting `coq-lsp`, in Visual Studio Code,
  `Ctrl+Shift+P` will give you access to the `coq-lsp.restart` command.
- In VSCode, the "Output" window will have a "Coq LSP Server Events"
  channel which should contain some important information.
- As of today, `coq-lsp` may have trouble when more than one file is open at
  the same time, this is a problem upstream. For now, you are advised to
  work on a single file if this problem appears.
- If you install `coq-lsp` simultaneously with VSCoq, VSCode gets confused and
  neither of them will work. Help with resolving this
  [issue](https://github.com/ejgallego/coq-lsp/issues/183) is extremely
  appreciated!

## Features

### Incremental compilation and continuous document checking:

Edit your file, and `coq-lsp` will try to re-check only what is necessary,
continuously. No more dreaded `Ctrl-C Ctrl-N`! Rechecking tries to be smart,
and will ignore whitespace changes.

<img alt="Incremental checking" height="286px" src="etc/img/lsp-incr.gif"/>

In a future release, `coq-lsp` will save its document cache to disk, so you can
restart your proof session where you left it at the last time.

Incremental support is undergoing refinement, if `coq-lsp` rechecks when it
should not, please file a bug!

### Smart, Cache-aware Error recovery

`coq-lsp` won't stop checking on errors, but supports (and encourages) working
with proof documents that are only partially working. Moreover, error recovery
integrates with the incremental cache, and will recognize proof structure.

You can edit without fear inside a `Proof. ... Qed.`, the rest of the document
won't be rechecked, unless the proof is completed.

### Whole-Document Goal Display

Press `Alt+Enter` (or `Cmd+Enter` in Mac) to show goals at point in a side
panel.

<img alt="Whole-Document Goal Display" height="286px" src="etc/img/lsp-goals.gif"/>

### Markdown support

Open a markdown file with a `.mv` extension, `coq-lsp` will check the code
parts! `coq-lsp` places human-friendly documents at the core of its design
ideas.

<img alt="Coq + Markdown Editing" height="286px" src="etc/img/lsp-markdown.gif"/>

### Document outline:

`coq-lsp` supports document outline and code folding, allowing you to jump
directly to definitions in the document.

<img alt="Document Outline Demo" height="286px" src="etc/img/lsp-outline.gif"/>

### Detailed timing and memory stats

Hover over any Coq sentence, `coq-lsp` will display detailed memory and timing
statistics.

<img alt="Stats on Hover" height="286px" src="etc/img/lsp-hover.gif"/>

### Client-side configuration options

`coq-lsp` is configurable, and tries to adapt to your own workflow. What to do
when a proof doesn't check, admit or ignore? You decide!

See the `coq-lsp` extension configuration in VSCode for options available.

<img alt="Configuration screen" height="286px" src="etc/img/lsp-config.png"/>

### Reusability, standards, modularity

The incremental document checking library of `coq-lsp` has been designed to be
reusable by other projects written in OCaml and with needs for document
validation UI, as well as by other Coq projects such as jsCoq.

Moreover, we are strongly based on standards, aiming for the least possible
extensions.

### A Platform for Research !

A key `coq-lsp` goal is to serve as central platform for researchers in
Human-Computer-Interaction, Machine Learning, and Software Engineering willing
to interact with Coq.

Towards this goal, `coq-lsp` extends and will eventually replace `coq-serapi`,
which has been used by many to that purpose.

### Planned features

See [planned features and contribution ideas](etc/ContributionIdeas.md) for a
list of things we plan to do, and tasks that you could take over.

## Protocol Notes

`coq-lsp` mostly implements the [LSP Standard](https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/), plus some extensions specific to Coq.

Check [the `coq-lsp` protocol documentation](etc/doc/PROTOCOL.md) for more details.

## Development / Building from sources

### Server:

To build the server, you'll need and environment with the dependencies stated
in `coq-lsp.opam`.

`make` will build the server at `_build/install/default/bin/coq-lsp`

### Nix

We have a Nix flake that you can use. For development, simply run `nix develop`.

If you wish to do `nix build` or compose this flake from another project, you
will need to use the .?submodules=1` trick, since we use submodules here for
vendoring. For example, building requires:

```
nix build .?submodules=1
```

You can use this flake in other flakes or Nix derviations.

### Visual Studio Code:

There are two ways to work with the VS Code extension: you can let VS Code
itself take care of building it (preferred setup), or you can build it manually.

First, run `npm install` in `editor/code`:

```sh
(cd editor/code && npm i)
```

That will setup the required packages as it is usual. You can run `package.json`
scripts the usual way:

```sh
(cd editor/code && npm run typecheck) # typecheck the project
(cd editor/code && npm run compile) # fast dev-transpile (no typecheck)
```

If you want to work with VS Code, these commands are not necessary, VS Code will
build the project automatically.

Launch VS Code using `dune exec -- code -n editor/code`, which will setup the
right environment variables such as `PATH` and `OCAMLPATH`, so the `coq-lsp`
binary can be found by VS Code. If you have installed `coq-lsp` globally, you
don't need `dune exec`, and can just run `code -n editor/code`.

Once in VS Code, you can launch the extension normally using the left "Run and
Debug" panel in Visual Studio Code, or the F5 keybinding.

You can of course install the extension in your `~/.vscode/` folder if so you
desire.

### Emacs

You can use `coq-lsp` with [eglot](https://joaotavora.github.io/eglot/).

If you find any trouble using `eglot` or `lsp-mode` with coq-lsp, please don't
hesitate to open an issue, Emacs support is a goal of `coq-lsp`.

### Roadmap

For now the main focus of the project to write clean and maintainable code, and
to provide a smooth user experience.

A core goal at this stage is to provide feedback upstream so the Coq API can be
tailored to provide a good interactive experience.

For the planned first release, we hope to provide a reasonable implementation
of core LSP features, editor support in VS Code.

### Code organization

`coq-lsp` consists of several components:

- `coq-serapi`: [vendored] improved utility functions to handle Coq AST
- `coq`: Utility library / abstracted Coq API. This is the main entry point for
  communication with Coq.
- `fleche`: incremental document processing backend. Exposes a generic API, but
  closely modelled to match LSP methods
- `lsp`: small generic LSP utilities, at some point to be replaced by a generic
  lib
- `controller`: LSP controller, a thin layer translating LSP transport layer to
  `flèche` surface API.

## Licensing information

The license for this project is LGPL 2.1 (or GPL 3+ as stated in the LGPL 2.1).

- This server forked from our previous LSP implementation in for the
  [Lambdapi](https://github.com/Deducteam/lambdapi) by Emilio J. Gallego Arias,
  Frédéric Blanqui, Rodolphe Lepigre, and others.

- Syntax files in editor/code are partially derived from
  [VSCoq](https://github.com/siegebell/vscoq) by Christian J. Bell, distributed
  under the terms of the MIT license (see ./vsc-galinas/License-vscoq.text).

## Team

- Ali Caglayan (co-coordinator)
- Emilio J. Gallego Arias (Inria Paris, co-coordinator)
- Shachar Itzhaky (Technion)
- Ramkumar Ramachandra

## Acknowledgments

Work on this server has been made possible thanks to many discussions,
inspirations, and sharing of ideas from colleagues. In particular, we'd like to
thank Rudi Grinberg, Andrey Mokhov, Clément Pit-Claudel, and Makarius Wenzel
for their help and advice.

As noted above, the original implementation was based on the Lambdapi LSP
server, thanks to all our collaborators in that project!

<!-- Local Variables: -->
<!-- mode: Markdown -->
<!-- fill-column: 80 -->
<!-- End: -->
