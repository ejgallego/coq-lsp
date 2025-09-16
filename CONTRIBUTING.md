Contributing to Coq LSP
=======================

Thank you very much for willing to contribute to coq-lsp!

The `coq-lsp` repository contains several tightly coupled components
in a single repository, also known as a monorepo, in particular:

- **base libraries**: `lang/`, `lsp/` which define common language constructs
- **Rocq API**: in `coq/`, an abstraction layer over Rocq's API
- **Flèche**: an incremental document engine for Rocq supporting
  literate programming and programability, in `fleche/`.
- **`fcc`**: an extensible command line compiler built on top of Flèche, in `compiler/`
- `petanque`: direct access to Coq's proof engine, in `petanque/`
- `coq-lsp`a LSP server for the Rocq Prover, in `controller/`
- Binaries for different platforms are in `lsp-server/$platform`
- **`coq-lsp/VSCode`**: a VSCode extension written in TypeScript and
  React, under `editor/code`

Read coq-lsp [FAQ](etc/FAQ.md) to learn more about LSP and
server/client roles. See more about code organization below.

It is possible to hack only in the server, on the client, or on both
at the same time. We have thus structured this guide in 3 sections:
general guidelines, server, and VS Code client.

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
license. We also allow licensing of our code under GPL 3+ and LGPL 2.1+.

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

## Server development guide

### Compilation

The server project uses a standard OCaml development setup based on
Opam and Dune.

The default development environment for `coq-lsp` is a "composed"
build that includes git submodules for `coq` and `coq-stdlib` in the
`vendor/` directory.

This allows to easily work with experimental Rocq branches, and some
other advantages like a better CI build cache and easier bisects.

This will however install a local Coq version which may not be
convenient for all use cases; we thus detail below an alternative
install method for those that would like to install a `coq-lsp`
development branch into an OPAM switch.

#### Default development setup, local Coq / `coq-lsp`

This setup will build Coq and `coq-lsp` locally; it is the recommended
way to develop `coq-lsp` itself.

1. Install the dependencies (the complete updated list of dependencies can be found in `coq-lsp.opam`).

    ```sh
    opam install --deps-only .
    ```

2. Initialize submodules (the `main` branch uses some submodules,
   which we plan to get rid of soon. Branches `v8.x` can already skip
   this step.)

    ```sh
    make submodules-init
    ```

3. Compile the server (the `coq-lsp` binary can be found in
`_build/install/default/bin/coq-lsp`).

    ```sh
    make
    ```

Alternatively, you can also use the regular `dune build @check` etc... targets.

Now, binaries for Coq and `coq-lsp` can be found under
`_build/install/default` and used via `dune exec -- fcc` or `dune exec
-- $your_editor`.

#### Global OPAM install

This setup will build Coq and `coq-lsp` and install them to the
current OPAM switch. This is a good setup for people looking to try
out `coq-lsp` development versions with other OPAM packages.

You can just do:
```
make submodules-init            # Only needed if submodules not initialized
make opam-update-and-reinstall
```

or alternatively, do it step by step

0. Be sure submodules and `coq-lsp` are up to date:a

    ```sh
    git pull --recurse-submodules
    ```

   alternatively you can use `make submodules-init` to refresh the
   submodules.

1. Install vendored Coq

    ```sh
    opam install vendor/coq/coq{-core,-stdlib,ide-server,}.opam
    ```

2. Install `coq-lsp`:
    ```sh
    opam install .
    ```

Then, you should get a working OPAM switch with Coq and `coq-lsp` from
your chosen `coq-lsp` branch.

#### Nix

We have a Nix flake that you can use.

1. Dependencies: for development it suffices to run `nix develop` to spawn a shell with the corresponding dependencies.

    With the following line you can save the configuration in a Nix profile which will prevent the `nix store gc` from deleting the entries:
    ```
    nix develop --profile nix/profiles/dev
    ```

    You can then use the following line to reuse the previous profile:
    ```
    nix develop nix/profiles/dev
    ```

2. Initialize submodules (the `main` branch uses some submodules, which we plan to get rid of soon. Branches `v8.x` can already skip this step.)

    ```sh
    make submodules-init
    ```

3. Compile the server (the `coq-lsp` binary can be found in
`_build/install/default/bin/coq-lsp`).

    ```sh
    make
    ```

You can view the list of packages and devShells that are exposed
by running `nix flake show`.

If you wish to do `nix build`, you will need to use the `.?submodules=1` trick,
since we use submodules here for vendoring. For example, building requires:

```
nix build .?submodules=1
```

This currently only applies to building the default package (`coq-lsp`), which is
the server. Clients don't have specific submodules as of yet.

When the flake is out-of-date, for instance when a new version of ocamlformat
is out, you can update the flake inputs with:
```sh
nix flake update
```

You can also add the `dev` version build to your flake as:
```nix
inputs.coq-lsp = { type = "git"; url = "https://github.com/ejgallego/coq-lsp.git"; submodules = true; };
...
coq-lsp.packages.${system}.default
```

### Code organization

The `coq-lsp` server consists of several components, we present them bottom-up

- `serlib`: utility functions to handle Coq AST
- `coq`: Utility library / abstracted Coq API. This is the main entry point for
  communication with Coq, and it reifies Coq calls as to present a purely
  functional interface to Coq.
- `lang`: base language definitions for Flèche
- `fleche`: incremental document processing backend. Exposes a generic API, but
  closely modelled to match LSP
- `lsp`: small generic LSP utilities, at some point to be replaced by a generic
  library
- `petanque`: low-level access to Coq's API
- `controller`: platform-agnostic LSP controller library, a thin layer
  translating LSP transport layer to `flèche` surface API.
- `lsp-server`: LSP server binaries for different platforms, using `controller`:
  + `native`: Native OCaml support, good for Windows, MacOS, and Linux.
  + `jsoo`: Javascript LSP server using [js_of_ocaml](https://ocsigen.org/js_of_ocaml/)

Some tips:

- we much prefer not to address Coq API directly, but always use the `coq`
  library to do it.
- `fleche` has carefully controlled dependencies and code structure due to a)
  having to run in JS, b) targeting other systems in addition to Coq.
- We use [ocamlformat][ocamlformat] to automatically format our codebase. `make
  fmt` will take care of it if your editor is not configured to so
  automatically.

[ocamlformat]: https://github.com/ocaml-ppx/ocamlformat

### Unicode setup

Flèche stores locations in the protocol-native format. This has the
advantage that conversion is needed only at range creation point
(where we usually have access to the document to perform the
conversion).

This way, we can send ranges to the client without conversion.

Request that work on the raw `Contents.t` buffer must do the inverse
conversion, but we handle this via a proper text API that is aware of
the conversion.

For now, the setup for Coq is:

- protocol-level (and Flèche) encoding: UTF-16 (due to LSP)
- `Contents.t`: UTF-8 (sent to Coq)

It would be very easy to set this parameters at initialization time,
ideal would be for LSP clients to catch up and allow UTF-8 encodings
(so no conversion is needed, at least for Coq), but it seems that we
will take a while to get to this point.

## Worker version (and debugging tips)

See https://github.com/ocsigen/js_of_ocaml/issues/410 for debugging
tips with `js_of_ocaml`.

## Client guide (VS Code Extension)

The VS Code extension is setup as a standard `npm` Typescript + React
package using `esbuild` as the bundler.

### Setup

1. Navigate to the editor folder
    ```sh
    cd editor/code
    ```
1. Install dependencies:
    ```sh
    npm i
    ```

Then there are two ways to work with the VS Code extension: you can let VS Code
itself take care of building it (preferred setup), or you can build it manually.

#### Let VS Code handle building the project

There is nothing to be done, VS Code will build the project
automatically when launching the extension. You can skip to [launching
the extension](#launch-the-extension).

#### Manual build

1. Navigate to the editor folder
    ```sh
    cd editor/code
    ```

You can now run `package.json` scripts the usual way:
- Typecheck the project
    ```sh
    npm run typecheck
    ```
- Fast dev-transpile (no typecheck)
    ```sh
    npm run compile
    ```

### Launch the extension

From the toplevel directory launch VS Code using `dune exec -- code -n
editor/code`, which will setup the right environment variables such as
`PATH` and `OCAMLPATH`, so the `coq-lsp` binary can be found by VS
Code. If you have installed `coq-lsp` globally, you don't need `dune
exec`, and can just run `code -n editor/code`.

Once in VS Code, you can launch the extension normally using the left "Run and
Debug" panel in Visual Studio Code, or the F5 keybinding.

You can of course install the extension in your `~/.vscode/` folder if so you
desire, although this is not recommended.

### Nix

In the case of the client we expose a separate shell, `client-vscode`,
which can be spawned with the following line (this can be done on top
of the original `nix develop`).

```
nix develop .#client-vscode
```

The steps to setup the client are similar to the manual build:
1. Spawn `develop` shell
    ```sh
    nix develop
    ```
2. Inside `develop`, spawn the `client-vscode` shell
    ```sh
    nix develop .#client-vscode
    ```
1. Navigate to the editor folder
    ```sh
    cd editor/code
    ```
1. Install dependencies:
    ```sh
    npm i
    ```
4. Follow the steps in [manual build](#manual-build).

You are now ready to [launch the extension](#launch-the-extension).

### Code organization
The extension is divided into two main folders:
- `editor/code/src/`: contains the main components,
- `editor/code/views`: contains some webviews components written using React.

### Testing the Web Extension

`coq-lsp` has preliminary support to run as a "Web Extension", to test
that, you want to use the web extension profile in the launch setup.

### Miscellaneous info

- The "Restart Coq LSP server" command will be of great help while developing
  with the server.
- We use [prettier][prettier] to automatically format files in `editor/code`.
  `make ts-fmt` will do this in batch mode.

[prettier]: https://marketplace.visualstudio.com/items?itemName=esbenp.prettier-vscode

### Debugging

The default build target will allow you to debug the extension by
providing the right sourcemaps.

### Nix:

Nix can be configured to use the version of the VS Code extension from
our `git` in the following way:

```nix
inputs.coq-lsp = { type = "git"; url = "https://github.com/ejgallego/coq-lsp.git"; submodules = true; };
...
programs.vscode = {
  enable = true;
  extensions = with pkgs.vscode-extensions; [
    ...
    inputs.coq-lsp.packages.${pkgs.system}.vscode-extension
    ...
  ];
};
```
## Test-suite

`coq-lsp` has a test-suite in the [test directory](./test), see the
README there for more details.

- `make test` will perform the LSP tests
- `make test-compiler` will perform the compiler tests

## Releasing

`coq-lsp` is released using `dune-release tag` + `dune-release`.

The checklist for the release as of today is the following:

### Prepare a release commit

- update the client changelog at `editor/code/CHANGELOG.md`, commit
- update the version number at `lsp-server/wasm/package.json`
- update the version number at `editor/code/package.json`
- do `make extension` to update the `package-lock.json` files
- update the version number at `fleche/version.ml`
- add release notes in `etc/release_notes/` if needed

### Tag and test release commit

```
export COQLSPV=0.2.5
git checkout main  &&                    opam exec --switch=dev-coq-lsp -- make && opam exec --switch=dev-coq-lsp -- make test test-compiler && dune-release tag ${COQLSPV}
git checkout v9.1  && git merge main  && opam exec --switch=rocq-v9.1   -- make && opam exec --switch=rocq-v9.1   -- make test test-compiler && dune-release tag ${COQLSPV}+9.1
git checkout v9.0  && git merge v9.1  && opam exec --switch=rocq-v9.0   -- make && opam exec --switch=rocq-v9.0   -- make test test-compiler && dune-release tag ${COQLSPV}+9.0
git checkout v8.20 && git merge v9.0  && opam exec --switch=coq-v8.20   -- make && opam exec --switch=coq-v8.20   -- make test test-compiler && dune-release tag ${COQLSPV}+8.20
git checkout v8.19 && git merge v8.20 && opam exec --switch=coq-v8.19   -- make && opam exec --switch=coq-v8.19   -- make test test-compiler && dune-release tag ${COQLSPV}+8.19
git checkout v8.18 && git merge v8.19 && opam exec --switch=coq-v8.18   -- make && opam exec --switch=coq-v8.18   -- make test test-compiler && dune-release tag ${COQLSPV}+8.18
git checkout v8.17 && git merge v8.18 && opam exec --switch=coq-v8.17   -- make && opam exec --switch=coq-v8.17   -- make test test-compiler && dune-release tag ${COQLSPV}+8.17
```

### Client release:

- build the JavaScript version `make js`
- build the extension with `npm run vscode:prepublish`
- check with `vsce ls` that the client contents are OK
- upload to official VSCode marketplace: `vsce publish`
- upload vsix to OpenVSX marketplace
- todo: check the wasm / js stuff is there, needs to improve

### Server:

`dune release` for each version that should to the main opam repos:

```
export COQLSPV=0.2.5
git checkout v9.1  && opam exec --switch=rocq-v9.1 -- dune-release
git checkout v9.0  && opam exec --switch=rocq-v9.0 -- dune-release
git checkout v8.20 && opam exec --switch=coq-v8.20 -- dune-release
git checkout v8.19 && opam exec --switch=coq-v8.19 -- dune-release
git checkout v8.18 && opam exec --switch=coq-v8.18 -- dune-release
git checkout v8.17 && opam exec --switch=coq-v8.17 -- dune-release
```

### [important] After release commit

- bump `version.ml` and `editor/code/package.json` version string to a `$version+1-dev`
