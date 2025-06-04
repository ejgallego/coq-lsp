# Rocq LSP <img align="right" height="42" src="./etc/img/inria-logo.png"/>  <!-- omit in toc -->

[![Github CI][ci-badge]][ci-link]

`coq-lsp` is a [Language Server](https://microsoft.github.io/language-server-protocol/) for the [Rocq Prover](https://coq.inria.fr). It provides a single server that implements:

- the [LSP](https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/)
  protocol, with custom [extensions](./etc/doc/PROTOCOL.md)
- the [petanque](./petanque) protocol, designed for low-latency interaction with
  Rocq, idel for AI and software engineering applications
- the [MCP](https://modelcontextprotocol.io/) protocol (upcoming), an open
  protocol that standardizes how applications provide context to LLMs

**Key [features](#Features)** of `coq-lsp` are: continuous, incremental document
checking, real-time interruptions and limits, programmable error recovery,
literate Markdown and LaTeX document support, multiple workspaces, positional
goals, information panel, performance data, completion, jump to definition,
extensible command-line compiler, a plugin system, and more.

`coq-lsp` is built on **Flèche**, a new document checking engine for formal
documents based on our previous work on
[SerAPI](https://github.com/ejgallego/coq-serapi/) and
[jsCoq](https://github.com/jscoq/jscoq).

Designed for interactive use and web-native environments, Flèche is extensible
and supports [advanced tooling integration](#-a-platform-for-research) and
capabilities beyond standard Rocq.

See the [User Manual](./etc/doc/USER_MANUAL.md) and the [General Documentation Index](./etc/doc/) for more details.

This repository also includes the `coq-lsp` [Visual Studio
Code](https://code.visualstudio.com/) editor extension for the [Rocq Proof
Assistant](https://coq.inria.fr), and a few other components. See our
[contributing guide](#contributing) for more information. Support
for [Emacs](#emacs), [Vim](#vim) and [Neovim](#neovim) is also available in
their own projects.

**Quick Install**:

  - **🐧 Linux / 🍎 macOs / 🪟 Windows:**
```
$ opam install coq-lsp && code --install-extension ejgallego.coq-lsp
```

  - **🪟 Windows:** (alternative method)

    Download the [Coq Platform installer](#-server)

  - **🦄 Emacs**:

```elisp
 (use-package rocq-mode
    :vc (:url "https://codeberg.org/jpoiret/rocq-mode.el.git"
         :rev :newest)
    :mode "\\.v\\'"
    :hook
    (rocq-mode . rocq-follow-viewport-mode)
    (rocq-mode . rocq-auto-goals-at-point-mode))
```

  - **☕ Try it online ☕ (experimental)**:

    https://github.dev/ejgallego/hello-rocq

## Table of Contents <!-- omit in toc -->

- [🎁 Features](#-features)
  - [⏩ Incremental Compilation and Continuous Document Checking](#-incremental-compilation-and-continuous-document-checking)
  - [👁 On-demand, Follow The Viewport Document Checking](#-on-demand-follow-the-viewport-document-checking)
  - [🧠 Smart, Cache-Aware Error Recovery](#-smart-cache-aware-error-recovery)
  - [🥅 Whole-Document Goal Display](#-whole-document-goal-display)
  - [🗒️ Markdown Support](#️-markdown-and-latex-support)
  - [👥 Document Outline](#-document-outline)
  - [🐝 Document Hover](#-document-hover)
  - [📁 Multiple Workspaces](#-multiple-workspaces)
  - [💾 `.vo` file saving](#-vo-file-saving)
  - [⏱️ Detailed Timing and Memory Statistics](#️-detailed-timing-and-memory-statistics)
  - [🔧 Client-Side Configuration Options](#-client-side-configuration-options)
  - [🖵 Extensible, Machine-friendly Command Line Compiler](#️-extensive-machine-friendly-command-line-compiler)
  - [♻️ Reusability, Standards, Modularity](#️-reusability-standards-modularity)
  - [🌐 Web Native!](#-web-native)
  - [🔎 A Platform for Research!](#-a-platform-for-research)
- [🛠️ Installation](#️-installation)
  - [🏘️ Supported Coq Versions](#️-supported-coq-versions)
  - [🏓 Server](#-server)
  - [🫐 Visual Studio Code](#-visual-studio-code)
  - [🦄 Emacs](#-emacs)
  - [✅ Vim](#-vim)
  - [🩱 Neovim](#-neovim)
  - [🐍 Python](#-python)
- [⇨ `coq-lsp` users and extensions](#-coq-lsp-users-and-extensions)
- [🗣️ Discussion Channel](#️-discussion-channel)
- [☎ Weekly Calls](#-weekly-calls)
- [❓FAQ](#faq)
- [⁉️ Troubleshooting and Known Problems](#️-troubleshooting-and-known-problems)
  - [📂 Working With Multiple Files](#-working-with-multiple-files)
- [📔 Planned Features](#-planned-features)
- [📕 Protocol Documentation](#-protocol-documentation)
- [🤸 Contributing and Extending the System](#-contributing-and-extending-the-system)
- [🥷 Team](#-team)
  - [🕰️ Past Contributors](#️-past-contributors)
- [©️ Licensing Information](#️-licensing-information)
- [👏 Acknowledgments](#-acknowledgments)

## 🎁 Features

### ⏩ Incremental Compilation and Continuous Document Checking

Edit your file, and `coq-lsp` will try to re-check only what is necessary,
continuously. No more dreaded `Ctrl-C Ctrl-N`! Rechecking tries to be smart,
and will ignore whitespace changes.

<img alt="Incremental checking" height="286px" src="etc/img/lsp-incr.gif"/>

In a future release, `coq-lsp` will save its document cache to disk, so you can
restart your proof session where you left it at the last time.

Incremental support is undergoing refinement, if `coq-lsp` rechecks when it
should not, please file a bug!

### 👁 On-demand, Follow The Viewport Document Checking

`coq-lsp` does also support on-demand checking. Two modes are available: follow
the cursor, or follow the viewport; the modes can be toggled using the Language
Status Item in Code's bottom right corner:

<img alt="On-demand checking" height="572px" src="etc/img/on_demand.gif"/>

### 🧠 Smart, Cache-Aware Error Recovery

`coq-lsp` won't stop checking on errors, but supports (and encourages) working
with proof documents that are only partially working. Error recovery integrates
with the incremental cache, and does recognize proof structure.

You can edit without fear inside a `Proof. ... Qed.`, the rest of the document
won't be rechecked; you can leave bullets and focused goals unfinished, and
`coq-lsp` will automatically admit them for you.

If a lemma is not completed, `coq-lsp` will admit it automatically. No more
`Admitted` / `Qed` churn!

<img alt="Smart error recovery" height="286px" src="etc/img/lsp-errors.gif"/>

### 🥅 Whole-Document Goal Display

`coq-lsp` will follow the cursor movement and show underlying goals and
messages; as well as information about what goals you have given up, shelves,
pending obligations, open bullets and their goals.

<img alt="Whole-Document Goal Display" height="286px" src="etc/img/lsp-goals.gif"/>

Goal display behavior is configurable in case you'd like to trigger goal display
more conservatively.

### 🗒️ Markdown and LaTeX Support

Open a markdown file with a `.mv` extension, or a `TeX` file ending in `.lv` or
`.v.tex`, then `coq-lsp` will check the code parts that are enclosed into `coq`
language blocks! `coq-lsp` places human-friendly documents at the core of its
design ideas.

<img alt="Coq + Markdown Editing" height="286px" src="etc/img/lsp-markdown.gif"/>

Moreover, you can use the usual Visual Studio Code Markdown or LaTeX preview
facilities to render your markdown documents nicely!

### 👥 Document Outline

`coq-lsp` supports document outline and code folding, allowing you to jump
directly to definitions in the document. Many of the Coq vernacular commands
like `Definition`, `Theorem`, `Lemma`, etc. will be recognized as document
symbols which you can navigate to or see the outline of.

<img alt="Document Outline Demo" height="286px" src="etc/img/lsp-outline.gif"/> <img alt="Document Symbols" height="286px" src="etc/img/lsp-doc-symbols.png"/>

### 🐝 Document Hover

Hovering over a Coq identifier will show its type.

<img alt="Types on Hover" height="286px" src="etc/img/lsp-hover-2.gif"/>

Hover is also used to get debug information, which can be enabled in the
preferences panel.

### 📁 Multiple Workspaces

`coq-lsp` supports projects with multiple `_CoqProject` files, use the "Add
folder to Workspace" feature of Visual Studio code or the LSP Workspace Folders
extension to use this in your project.

### 💾 `.vo` file saving

`coq-lsp` can save a `.vo` file of the current document as soon as it the
checking has been completed, using the command `Coq LSP: Save file to .vo`.

You can configure `coq-lsp` in settings to do this every time you save your
`.vo` file, but this can be costly so we ship it disabled by default.

### ⏱️ Detailed Timing and Memory Statistics

Hover over any Coq sentence, `coq-lsp` will display detailed memory and timing
statistics.

<img alt="Stats on Hover" height="286px" src="etc/img/lsp-hover.gif"/>

### 🔧 Client-Side Configuration Options

`coq-lsp` is configurable, and tries to adapt to your own workflow. What to do
when a proof doesn't check, admit or ignore? You decide!

See the `coq-lsp` extension configuration in VSCode for options available.

<img alt="Configuration screen" height="286px" src="etc/img/lsp-config.png"/>

### 🖵 Extensible, Machine-friendly Command Line Compiler

`coq-lsp` includes the `fcc` "Flèche Coq Compiler" which allows the access to
almost all the features of Flèche / `coq-lsp` without the need to spawn a
fully-fledged LSP client.

`fcc` has been designed to be machine-friendly and extensible, so you can easily
add your pre/post processing passes, for example to analyze or serialize parts
of Coq files.

### 🪄 Advanced APIs for Coq Interaction

Thanks to Flèche, we provide some APIs on top of it that allow advanced use
cases with Coq. In particular, we provide direct, low-overhead access to Coq's
proof engine using [petanque](./petanque).

### ♻️ Reusability, Standards, Modularity

The incremental document checking library of `coq-lsp` has been designed to be
reusable by other projects written in OCaml and with needs for document
validation UI, as well as by other Coq projects such as jsCoq.

Moreover, we are strongly based on standards, aiming for the least possible
extensions.

### 🌐 Web Native!

`coq-lsp` has been designed from the ground up to fully run inside your web
browser seamlessly; our sister project, [jsCoq](https://github.com/jscoq/jscoq)
has been already been experimentally ported to `coq-lsp`, and future releases
will use it by default.

`coq-lsp` provides an exciting new array of opportunities for jsCoq, lifting
some limitations we inherited from Coq's lack of web native support.

### 🔎 A Platform for Research!

A key `coq-lsp` goal is to serve as central platform for researchers in
Human-Computer-Interaction, Machine Learning, and Software Engineering willing
to interact with Coq.

Towards this goal, `coq-lsp` extends and is in the process of replacing [Coq
SerAPI](https://github.com/ejgalleg/coqserapi), which has been used by many to
that purpose.

If you are a SerAPI user, please see our preliminary [migrating from
SerAPI](etc/SerAPI.md) document.

## 🛠️ Installation

In order to use `coq-lsp` you'll need to install [**both**](etc/FAQ.md)
`coq-lsp` and a suitable LSP client that understands `coq-lsp` extensions. The
recommended client is the Visual Studio Code Extension, but we aim to fully
support other clients officially and will do so once their authors consider them
ready.

### 🏘️ Supported Coq Versions

`coq-lsp` supports Rocq 9.0, Coq 8.20, Coq 8.19, Coq 8.18, Coq 8.17, and Coq's
`master` branch.  Code for each Coq version can be found in the corresponding
branch.

We recommended using Rocq 9.0 or `master` version. For other Coq versions, we
recommend users to install the custom Coq tree as detailed in [Coq Upstream
Bugs](#coq-upstream-bugs).

Note that this section covers user installs, if you would like to contribute to
`coq-lsp` and build a development version, please check our [contributing
guide](./CONTRIBUTING.md)

### 🏓 Server

- **opam** (OSX/Linux):
  ```
  opam install coq-lsp
  ```
- **Nix**:
  - In nixpkgs: [coqPackages.coq-lsp](https://github.com/NixOS/nixpkgs/tree/master/pkgs/development/coq-modules/coq-lsp)
  - The `coq-lsp` server is automatically put in scope when running `nix-shell` in a
    project using the [Coq Nix Toolbox](https://github.com/coq-community/coq-nix-toolbox)
    (added to the toolbox Oct 10th 2023).
  - An example of a `flake` that uses `coq-lsp` in a development environment is here
     https://github.com/HoTT/Coq-HoTT/blob/master/flake.nix .
- **Windows**:
  Experimental Windows installers based on the [Coq
  Platform](https://github.com/coq/platform) are available at https://www.irif.fr/~gallego/coq-lsp/

  This provides a Windows native binary that can be executed from VSCode
  normally. As of today a bit of configuration is still needed:
  - In VSCode, set the `Coq-lsp: Path` to:
    + `C:\Coq-Platform~8.20-lsp\bin\coq-lsp.exe`
  - In VSCode, set the `Coq-lsp: Args` to:
    + `--coqlib=C:\Coq-Platform~8.20-lsp\lib\coq\`
    + `--coqcorelib=C:\Coq-Platform~8.20-lsp\lib\coq-core\`
    + `--ocamlpath=C:\Coq-Platform~8.20-lsp\lib\`
  - Replace `C:\Coq-Platform~8.20-lsp\` by the path you have installed Coq above as needed
  - Note that the installers are unsigned (for now), so you'll have to click on
    "More info" then "Run anyway" inside the "Windows Protected your PC" dialog
  - Also note that the installers are work in progress, and may change often.
- **Do it yourself!** [Compilation from sources](./CONTRIBUTING.md#compilation)

<!-- TODO 🟣 Emacs, 🪖 Proof general, 🐔 CoqIDE -->

### 🫐 Visual Studio Code

- Official Marketplace: https://marketplace.visualstudio.com/items?itemName=ejgallego.coq-lsp
- Open VSX: https://open-vsx.org/extension/ejgallego/coq-lsp

### 🦄 Emacs

The official Rocq Emacs mode is https://codeberg.org/jpoiret/rocq-mode.el ,
maintained by Josselin Poiret with contributions by Arthur Azevedo de Amorim.

### ✅ Vim

- Experimental [CoqTail](https://github.com/whonore/Coqtail) support by Wolf Honore:
  https://github.com/whonore/Coqtail/pull/323

  See it in action https://asciinema.org/a/mvzqHOHfmWB2rvwEIKFjuaRIu

### 🩱 Neovim

- Experimental client by Jaehwang Jung: https://github.com/tomtomjhj/coq-lsp.nvim

### 🐍 Python

- Interact programmatically with Coq files by using the [Coqpyt](https://github.com/sr-lab/coqpyt)
  by Pedro Carrott and Nuno Saavedra.

## ⇨ `coq-lsp` users and extensions

The below projects are using `coq-lsp`, we recommend you try them!

- [Coqpyt, a Python client for coq-lsp](https://github.com/sr-lab/coqpyt)
- [CoqPilot uses Large Language Models to generate multiple potential proofs and then uses coq-lsp to typecheck them](https://github.com/JetBrains-Research/coqpilot).
- [jsCoq: use Coq from your browser](https://github.com/jscoq/jscoq)
- [Pytanque: a Python library implementing RL Environments](https://github.com/LLM4Coq/pytanque)
- [ViZX: A Visualizer for the ZX Calculus](https://github.com/inQWIRE/ViZX).
- [The Waterproof vscode extension helps students learn how to write mathematical proofs](https://github.com/impermeable/waterproof-vscode).
- [Yade: Support for the YADE diagram editor in VSCode](https://github.com/amblafont/vscode-yade-example).

## 🗣️ Discussion Channel

`coq-lsp` discussion channel it at [Coq's
Zulip](https://coq.zulipchat.com/#narrow/stream/329642-coq-lsp), don't hesitate
to stop by; both users and developers are welcome.

## ☎ Weekly Calls

We hold (almost) weekly video conference calls, see the [Call Schedule
Page](https://github.com/ejgallego/coq-lsp/wiki/Coq-Lsp-Calls) for more
information. Everyone is most welcome!

## ❓FAQ

See our [list of frequently-asked questions](./etc/FAQ.md).

## ⁉️ Troubleshooting and Known Problems

### Coq upstream bugs

Unfortunately Coq releases contain bugs that affect `coq-lsp`. We strongly
recommend that if you are installing via opam, you use the following branches
that have some fixes backported:

- For 8.20: No known problems
- For 8.19: `opam pin add coq-core https://github.com/ejgallego/coq.git#v8.19+lsp`
- For 8.18: `opam pin add coq-core https://github.com/ejgallego/coq.git#v8.18+lsp`
- For 8.17: `opam pin add coq-core https://github.com/ejgallego/coq.git#v8.17+lsp`

### Known problems

- Current rendering code can be slow with complex goals and messages, if that's
  the case, please open an issue and set the option `Coq LSP > Method to Print
  Coq Terms` to 0 as a workaround.
- `coq-lsp` can fail to interrupt Coq in some cases, such as `Qed` or type class
  search. If that's the case, please open an issue, we have a experimental
  branch that solves this problem that you can try.
- Working with multiple files in Coq < 8.17 requires a Coq patch, see below for
  instructions.
- If you install `coq-lsp/VSCode` simultaneously with the `VSCoq` Visual Studio
  Code extension, Visual Studio Code gets confused and neither of them may
  work. `coq-lsp` will warn about that. You can disable the `VSCoq` extension as
  a workaround.
- `_CoqProject` file parsing library will often `exit 1` on bad `_CoqProject`
  files! There is little `coq-lsp` can do here, until upstream fixes this.

### Troubleshooting

- Some problems can be resolved by restarting `coq-lsp`, in Visual Studio Code,
  `Ctrl+Shift+P` will give you access to the `coq-lsp.restart` command.
  You can also start / stop the server from the status bar.
- In VSCode, the "Output" window will have a "Coq LSP Server Events" channel
  which should contain some important information; the content of this channel
  is controlled by the `Coq LSP > Trace: Server` option.

## 📔 Planned Features

See [planned features and contribution ideas](etc/ContributionIdeas.md) for a
list of things we'd like to happen.

## 📕 Protocol Documentation

`coq-lsp` mostly implements the [LSP
Standard](https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/),
plus some extensions specific to Coq.

Check [the `coq-lsp` protocol documentation](etc/doc/PROTOCOL.md) for more details.

## 🤸 Contributing and Extending the System

Contributions are very welcome! Feel free to chat with the dev team in
[Zulip](https://coq.zulipchat.com/#narrow/stream/329642-coq-lsp) for any
question, or just go ahead and hack.

We have a [contributing guide](CONTRIBUTING.md), which includes a description of
the organization of the codebase, developer workflow, and more.

Here is a [list of project ideas](etc/ContributionIdeas.md) that could be of
help in case you are looking for contribution ideas, tho we are convinced that
the best ideas will arise from using `coq-lsp` in your own Coq projects.

Both Flèche and `coq-lsp` have a preliminary _plugin system_. The VSCode
extension also exports and API so other extensions use its functionality
to query and interact with Coq documents.

## 🥷 Team

- Ali Caglayan (co-coordinator)
- Emilio J. Gallego Arias (Inria Paris, co-coordinator)
- Shachar Itzhaky (Technion)

### 🕰️ Past Contributors

- Vincent Laporte (Inria)
- Ramkumar Ramachandra (Inria Paris)

## ©️ Licensing Information

The license for this project is LGPL 2.1 (or GPL 3+ as stated in the LGPL 2.1).

- This server forked from our previous LSP implementation for the
  [Lambdapi](https://github.com/Deducteam/lambdapi) proof assistant, written by
  Emilio J. Gallego Arias, Frédéric Blanqui, Rodolphe Lepigre, and others; the
  initial port to Coq was done by Emilio J. Gallego Arias and Vicent Laporte.

- Syntax files in editor/code are partially derived from
  [VSCoq](https://github.com/siegebell/vscoq) by Christian J. Bell, distributed
  under the terms of the MIT license (see ./editor/code/License-vscoq.text).

## 👏 Acknowledgments

Work on this server has been made possible thanks to many discussions,
inspirations, and sharing of ideas from colleagues. In particular, we'd like to
thank Rudi Grinberg, Andrey Mokhov, Clément Pit-Claudel, and Makarius Wenzel for
their help and advice. Gaëtan Gilbert contributed many key and challenging Coq
patches essential to `coq-lsp`; we also thank Guillaume Munch-Maccagnoni for his
[memprof-limits](https://guillaume.munch.name/software/ocaml/memprof-limits/index.html)
library, which is essential to make `coq-lsp` on the real world, as well for
many advice w.r.t. OCaml.

As noted above, the original implementation was based on the Lambdapi LSP
server, thanks to all the collaborators in that project!

[ci-badge]: https://github.com/ejgallego/coq-lsp/actions/workflows/build.yml/badge.svg
[ci-link]: https://github.com/ejgallego/coq-lsp/actions/workflows/build.yml

<!-- Local Variables: -->
<!-- mode: Markdown -->
<!-- fill-column: 80 -->
<!-- End: -->
