## coq-lsp Web Worker README

This directory contains the implementation of our LSP-compliant web
worker for Coq, based on jsCoq.

As you can see the implementation is minimal, thanks to proper
abstraction of the core of the controller.

For now it is only safe to use the worker in 32bit OCaml mode.

Support for this build is still experimental. See [the javascript
compilation
meta-issue](https://github.com/ejgallego/coq-lsp/issues/833) for more
information.

## Building the Worker

The worker needs two parts to work:

- the worker binary
- the worker OCaml filesystem (`controller-js/coq-fs-core.js`)
- the worker Coq filesystem (`controller-js/coq-fs.js`)

which are then bundled in a single `.js` file.

The worker OCaml filesystem includes:
- `META` files for anything used by Coq
- transpiled `.cma` to `.js` files for plugins that will be loaded by Coq

Type:

```
make patch-for-js                 # (only once, patch Coq for JS build)
make controller-js/coq-fs-core.js # build the OCaml filesystem, needed when plugins change
make js                           # build the worker and link with the FS.
```
to get a working build in `editor/code/out`.

As of now the build is very artisanal and not flexible at all, we hope to improve it soon.

## Testing the worker

You can test the server using any of the [official methods](https://code.visualstudio.com/api/extension-guides/web-extensions#test-your-web-extension).

Using the regular setup `dune exec -- code editor/code` and then
selecting "Web Extension" in the run menu works out of the box.

A quick recipe from the manual is:

```
$ make controller-js/coq-fs-core.js && make js
$ npx @vscode/test-web --browser chromium --extensionDevelopmentPath=editor/code
$ chrome localhost:3000
```

you can also download the artifacts from the CI build, and point
`--extensionDevelopmentPath=` to the path you have downloaded the
extension + Coq build.

## COI

As of Feb 2023, due to security restrictions, you may need to either:

 - pass `--enable-coi` to `code`
 - append `?vscode-coi` in the vscode dev setup URL

in order to have interruptions (`SharedBufferArray`) working.

See https://code.visualstudio.com/updates/v1_72#_towards-cross-origin-isolation

## WASM

We hope to have a WASM backend working soon, based on waCoq, see
https://github.com/microsoft/vscode-wasm

## Filesystem layout

We need to have most `META` files in findlib, plus the Coq and
`coq-lsp.serlib.*` plugins. These should be precompiled.

- `/static/lib`: OCaml findlib root
- `/static/coqlib`: Coq root, with regular paths
  + `/static/coqlib/theories`
  + `/static/coqlib/user-contrib`
