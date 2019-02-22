## Coq LSP

## Editor support

### Emacs

You can use eglot with `$path_to_server --std`. Note that std is
needed otherwise eglot will choke.

### Visual Studio Code

 1. Symlink the `editor/vscoq` directory into `~/.vscode/extensions/`.
 2. Run `npm install` in the `./vscoq` directory.
 3. Install the server (`nix-env -if .`).
 4. Run VS Code and visit a `.v` file.

In case you are developing the server/controller, you can, instead of 3-4 above:

 3. Build the controller (in an appropriate environment, e.g., `nix-shell`)
    using `make`
 4. Launch VS Code through `dune`: `dune exec code`

## Design

The worker protocol is designed to be as stateless as possible.

## Licensing information

This work is partially derived from:

  - [VSCoq](https://github.com/siegebell/vscoq) by Christian J. Bell, distributed under the terms of the MIT license
    (see ./vsc-galinas/License-vscoq.text).
