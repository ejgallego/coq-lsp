# Multiple workspaces setup

## How to run it:

Try to load the `example.code-workspace` file in VSCode.

You may need to compile the right `.vo` files for the imports to
work. You can do that with the `Save VO command`; as of now, `coq-lsp`
will require you do this before opening the depending files.

`coq-lsp` will take care of this automatically in the next version,
including the auto-update. You can also do:

```sh
$ coqc -R bar bar bar/barx.y
$ coqc -R foo foo foo/foox.y
```

## `coq-lsp` workspace documentation

For each workspace added to a project, `coq-lsp` will try to configure
it by searching for a `_CoqProject` file, then it will apply the
options found there. In the near future, we will also detect
`dune-project` files at the root too.

`coq-lsp` does determine the workspace roots using the standard
methods provided by the LSP protocol, in particular `wsFolders`,
`rootURI`, and `rootPath` at initialiation, in this order; and by
listening to the `workspace/didChangeWorkspaceFolders` notification
after initialization.

## Known problems

When projects are using Coq plugins, `findlib` doesn't properly
support having multiple roots in the same process. We are using a hack
that seems to work (we reinitialize `findlib`), however the hack is
very fragile; we should improve `findlib` upstream to support our use
case.
