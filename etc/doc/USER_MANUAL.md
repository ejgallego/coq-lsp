# `coq-lsp` user manual

Welcome to `coq-lsp` in-progress user-manual.

Please see also `coq-lsp` FAQ.

## First steps with `coq-lsp`

`coq-lsp` is designed to work on a project-basis, that is to say, the
user should point to the _root_ of their project (for example using
"Open Folder" in VSCode).

Given a project root `dir`, `coq-lsp` will try to read
`$dir/_RocqProject` (or `$dir/_CoqProject` if the first is not
detected) and will apply the settings for your project from there.

Other tools included in the `coq-lsp` suite usually take a
`--root=dir` command line parameter to set this information up.

`coq-lsp` will display information about the project root and setting
auto-detection using the standard language server protocol messaging
facilities. In VSCode, these settings can be usually displayed in the
"Output > Coq-lsp server" window.

## Key features:

### Continuous vs on-demand mode

`coq-lsp` offers two checking modes:

- continuous checking [default]: `coq-lsp` will check all your open
  documents eagerly. This is best when working with powerful machines
  to minimize latency. When using OCaml 4.x, `coq-lsp` uses the
  `memprof-limits` library to interrupt Coq and stay responsive.

- on-demand checking [set the `check_only_on_request` option]: In this
  mode, `coq-lsp` will stay idle and only compute information that is
  demanded, for example, when the user asks for goals. This mode
  disables some useful features such as `documentSymbol` as they can
  only be implemented by checking the full file.

  This mode can use the `check_on_scroll` option, which improves
  latency by telling `coq-lsp` to check eagerly what is on view on
  user's screen.

Users can change between on-demand/continuous mode by clicking on the
"Coq language status" item in the bottom right corner for VSCode. We
recommend pinning the language status item to see server status in
real-time.

### Goal display

By default, `coq-lsp` will follow cursor and show goals at cursor
position. This can be tweaked in options.

The `coq-lsp.sentenceNext` and `coq-lsp.sentencePrevious` commands will
try to move the cursor one Coq sentence forward / backwards. These
commands are bound by default to `Alt + N` / `Alt + P` (`Cmd` on
MacOS).

### Incremental proof edition

Once you have setup your basic proof style, you may want to work with
`coq-lsp` in a way that is friendly to incremental checking.

For example, `coq-lsp` will recognize blocks of the form:
```coq
Lemma foo : T.
Proof.
 ...
Qed.
```

and will allow you to edit inside the `Proof.` `Qed.` block without
re-checking what is outside.

### Error recovery

`coq-lsp` can recover many errors automatically and allow you to
continue document edition later on.

For example, it is not necessary to put `Admitted` in proofs that are
not fully completed. Also, you can work with bullets and `coq-lsp`
will automatically admit unfinished ones, so you can follow the
natural proof structure.

### Server Status



### Embedded Markdown and LaTeX documents

`coq-lsp` supports checking of TeX and Markdown document with embedded
Coq inside. As of today, to enable this feature you must:

- **markdown**: open a file with `.mv` extension, `coq-lsp` will
  recognize code blocks starting with ````coq` and ````rocq`.
- **TeX**: open a file with `.lv` extension, `coq-lsp` will recognize
  code blocks delimited by `\begin{coq} ... \end{coq}`

As of today, delimiters are expected at the beginning of the line,
don't hesitate to request for further changes based on this feature.

## Coq LSP Settings

### Goal display

Several settings for goal display exist.

### Continuous vs on-demand mode:

A setting to have `coq-lsp` check documents continuously exists.

## Memory management

You can tell the server to free up memory with the "Coq LSP: Free
memory" command.

## Advanced: Multiple Workspaces

`coq-lsp` does support projects that combine multiple Coq project
roots in a single workspace. That way, one can develop on several
distinct Coq developments seamlessly.

To enable this, use the "Add Folder" option in VSCode, where each root
must be a folder containing a `_CoqProject` file.

Check the example at
[../../examples/multiple_workspaces/](../../examples/multiple_workspaces/)
to see it in action!

## Interrupting coq-lsp

When a Coq document is being checked, it is often necessary to
_interrupt_ the checking process, for example, to check a new version,
or to retrieve some user-facing information, such as goals.

`coq-lsp` supports two different interruption methods, selectable at
start time via the `--int_backend` command-line parameter:

- Coq-side polling (`--int_backend=Coq`, default for OCaml 5.x): in
  this mode, Coq polls for a flag every once in a while, and will
  raise an interruption when the flag is set. This method has the
  downside that some paths in Coq don't check the flag often enough,
  for example, `Qed.`, so users may face unresponsiveness, as our
  server can only run one thread at a time.

- `memprof-limits` token-based interruption (`--int_backend=Mp`,
  experimental, default for OCaml 4.x): in this mode, Coq will use the
  `memprof-limits` library to interrupt Coq.

Coq has some bugs w.r.t. handling of asynchronous interruptions coming
from `memprof-limits`. The situation is better in Coq 8.20, but users
on Coq <= 8.19 do need to install a version of Coq with the backported
fixes. See the information about Coq upstream bugs in the README for
more information about available branches.

`coq-lsp` will reject to enable the new interruption mode by default
on Coq < 8.20 unless the `lsp` Coq branch version is detected.

## Advanced incremental tricks

You can use the `Reset $id` and `Back $steps` commands to isolate
parts of the document from each other in terms of rechecking.

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
