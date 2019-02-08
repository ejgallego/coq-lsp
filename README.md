## Coq LSP

## Editor support

### Emacs

You can use eglot with `$path_to_server --std`. Note that std is
needed otherwise eglot will choke.

## Design

The worker protocol is designed to be as stateless as possible.
