Contributing to Coq LSP
=======================

Thank you very much for willing to contribute to coq-lsp!

`coq-lsp` has two components:

- a LSP server for Coq project written in OCaml.
- a `coq-lsp` VS Code extension written in TypeScript and React, in
  the `editor/code` directory.

Read coq-lsp [FAQ](etc/FAQ.md) for an explanation on what the above mean.

It is possible to hack only in the server, on the client, or on both at the same
time. We have thus structured this guide in 3 sections: general guidelines,
server, and VS Code client.

## General guidelines

`coq-lsp` is developed in an open-source manner using GitHub.

### Zulip chat

Our main development channel is [hosted at
Zulip](https://coq.zulipchat.com/#narrow/stream/329642-coq-lsp)
. Please don't hesitate to stop by if you have any questions.

### Code of conduct

All contributors of `coq-lsp` must agree to our [code of
conduct](./CODE_OF_CONDUCT.md)

### License

`coq-lsp` uses the LGPL 2.1 license, which is compatible with Coq's
license.

### Submitting a contribution, opening an issue.

Please use the github standard interfaces to do so. When you submit a
pull request, you agree to share your code under `coq-lsp` license.

We have a set of tags to classify pull requests and issues, we try to use them
as much as possible. As of today, GitHub requires some permissions for regular
users to be able to manipulate this meta-data, let us know if you need access.

### Changelog

We require an entry in `CHANGES.md` for all changes of relevance; note that as
of today, `CHANGES.md` is the canonical changelog for _both_ the server and the
client.

The client changelog that is used by the VS Code marketplace is at
`editor/code/CHANGELOG.md`, but you should not modify it, as of today we will
generate it from the relevant entries in `CHANGES.md` at release time.

## Server guide

### Compilation

The server project uses a standard OCaml development setup based on Opam and
Dune.

To build it, you'll need an environment with the dependencies stated in
`coq-lsp.opam`.

`make` will compile the server (the `coq-lsp` binary, to be found in
`_build/install/default/bin/coq-lsp`).

As of today the `main` branch uses some submodules, be sure they are properly
initialized (`make submodules-init`).

(We plan to get rid of the submodules soon)

You can also use the regular `dune build @check` etc... targets.

#### Nix

We have a Nix flake that you can use. For development, in the case of the
server, simply run `nix develop`.

If you do
```
nix develop --profile nix/profiles/dev
```

You can save the configuration in a Nix profile which will prevent the `nix
store gc` from deleting the entries.

You can do:
```
nix develop nix/profiles/dev
```
To reuse the same profile.

In the case of the client, we expose separate shells, e.g client-vscode, would
be
```
nix develop .#client-vscode
```
(this can be done on top of the original `nix develop`)

You can view the list of packages and devShells that are exposed
by running `nix flake show`.

To build you can do:
```
nix build .
```


#### Releasing

`coq-lsp` is released using `dune-release tag` + `dune-release`.

The checklist for the release as of today is:

##### Client:

- update the client changelog at `editor/code/CHANGELOG.md`, commit
- for the `main` branch: `dune release tag $coq_lsp_version`
- check with `vsce ls` that the client contents are OK
- `vsce publish`

##### Server:

- sync branches for previous Coq versions, using `git merge`, test and push to CI.
- `dune release tag` for each `$coq_lsp_version+$coq_version`
- `dune release` for each version that should to the main Coq repos
- [optional] update pre-release packages to coq-opam-archive
- [important] bump `version.ml` and `package.json` version string

### Code organization

The `coq-lsp` server consists of several components, we present them bottom-up

- `vendor/coq-serapi`: [vendored] improved utility functions to handle Coq AST
- `coq`: Utility library / abstracted Coq API. This is the main entry point for
  communication with Coq, and it reifies Coq calls as to present a purely
  functional interface to Coq.
- `fleche`: incremental document processing backend. Exposes a generic API, but
  closely modelled to match LSP
- `lsp`: small generic LSP utilities, at some point to be replaced by a generic
  library
- `controller`: LSP controller, a thin layer translating LSP transport layer to
  `flèche` surface API, plus some custom event queues for Coq.
- `controller-js`: LSP controller for Javascript, used for `vscode.dev` and
  jsCoq.

Some tips:

- we much prefer not to address Coq API directly, but always use the `coq`
  library to do it.
- `fleche` has carefully controlled dependencies and code structure due to a)
  having to run in JS, b) targeting other systems in addition to Coq.
- We use [ocamlformat][ocamlformat] to automatically format our codebase. `make
  fmt` will take care of it if your editor is not configured to so
  automatically.

[ocamlformat]: https://github.com/ocaml-ppx/ocamlformat

## VS Code Extension guide

The VS Code extension is setup as a standard `npm` type-script + React package
using `esbuild` as the bundler. The extension has a main component in
`editor/code/src/` and some webviews components written using React under
`editor/code/views`.

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
desire, tho this is not recommended.

### Miscellaneous info

- The "Restart Coq LSP server" command will be of great help while developing
  with the server.
- We use [prettier][prettier] to automatically format files in editor/code.
  `make ts-fmt` will do this in batch mode.

[prettier]: https://marketplace.visualstudio.com/items?itemName=esbenp.prettier-vscode

### Debugging

The default build target will allow you to debug the extension by providing the
right sourcemaps.

## Emacs

You should be able to use `coq-lsp` with
[eglot](https://joaotavora.github.io/eglot/).

If you find any trouble using `eglot` or `lsp-mode` with coq-lsp, please don't
hesitate to open an issue, Emacs support is a goal of `coq-lsp`.

# VIM

`coq-lsp` should also run on VIM, VIM/NeoVIM support is a goal of `coq-lsp`
