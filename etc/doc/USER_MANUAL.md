# `coq-lsp` user manual

Welcome to `coq-lsp` in-progress user-manual.

Please see also `coq-lsp` FAQ.

## First steps with `coq-lsp`

`coq-lsp` is designed to work on a project-basis, that is to say, the
user should point to the _root_ of their project (for example using
"Open Folder" in VSCode).

Given a project root `dir`, `coq-lsp` will try to read
`$dir/_CoqProject` and will apply the settings for your project from
there.

Other tools included in the `coq-lsp` suite usually take a
`--root=dir` command line parameter to set this information.

`coq-lsp` will display information about the project root and setting
auto-detection using the standard language server protocol messaging
facilities. In VSCode, these settings can be usually displayed in the
"Output > Coq-lsp server" window.

## Selecting the interruption backend

When a Coq document is being checked, it is often necessary to
_interrupt_ the checking process, for example, to check a new version,
or to retrieve some user-facing information.

`coq-lsp` supports two interruption methods, selectable at start time
via the `--int_backend` command-line parameter:

- Coq-side polling (`--int_backend=Coq`, default): in this mode, Coq
  polls for a flag every once in a while, and will raise an
  interruption when the flag is set. This method has the downside that
  some paths in Coq don't check the flag often enough, for example,
  `Qed.`, so users may face unresponsiveness, as our server can only
  run one thread at a time.

- `memprof-limits` token-based interruption (`--int_backend=Mp`,
  experimental): in this mode, Coq will use the `memprof-limits`
  library to interrupt Coq.

Coq has some bugs w.r.t. handling of asynchronous interruptions coming
from `memprof-limits`. The situation is better in Coq 8.20, but users
on Coq <= 8.19 do need to install a version of Coq with the backported
fixes. See the information about Coq upstream bugs in the README for
more information about available branches.

## Advanced incremental tricks

You can use the `Reset $id` and `Back $steps` commands to isolate
parts of the document from each others in terms of rechecking.

For example, the command `Reset $id` will make the parts of the
document after it use the state before the node `id` was found. Thus,
any change between `$id` and the `Reset $id` command will not trigger
a recheck of the rest of the document.

```coq
(* Coq code 1 *)

Lemma foo : T.
Proof. ... Qed.

(* Coq code 2 *)

Reset foo.

(* Coq code 3 *)
```

In the above code, any change in the "`Coq code 2`" section will not
trigger a recheck of the "`Coq code 3`" Section, by virtue of the
incremental engine.

Using `Reset Initial`, you can effectively partition the document on
`N` parts! This is pretty cool for some use cases!
