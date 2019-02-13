## Coq LSP

## Editor support

### Emacs

You can use eglot with `$path_to_server --std`. Note that std is
needed otherwise eglot will choke.

### VS-Code

 1. Symlink the `vsc-galinas` directory into `~/.vscode/extensions/`.
 2. Run `npm install` in that repository.
 3. Install the server (`nix-env -if .`).
 4. Run VS-Code and visit a `.v` file.

## Design

The worker protocol is designed to be as stateless as possible.

## Licensing information

This work is partially derived from:

  - [VSCoq](https://github.com/siegebell/vscoq) by Christian J. Bell, distributed under the terms of the MIT license
    (see ./vsc-galinas/License-vscoq.text).

