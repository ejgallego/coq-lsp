## Migrating from Coq SerAPI to `coq-lsp`

Welcome fellow SerAPI user, first of all, a reminder that is of
crucial importance for us to keep maintaining both coq-lsp and
Coq SerAPI: we need to hear from your use case.

Please, if you are using `coq-lsp` and / or SerAPI for research, open
a pull request so we can link to your work in our readme.

With that being said, here go a few notes on migrating from SerAPI to
`coq-lsp`.

### Sexp vs JSONRpc

`coq-lsp` is based on the Language Standard Protocol and uses JSON as
the main communication format. Several libraries exist to talk to LSP
servers. The main difference, in addition to the format, and using a
widespread standard for many operations, is that `coq-lsp` provides a
_request_ and _notification_ RPC call.

### Add vs `didChange`

`coq-lsp` does away with the "sentence" model underlying in SerAPI,
and now documents are understood as a whole. Document can contain
markdown, images, JSON, and a variety of other data in addition to
Coq.

`coq-lsp` understands incremental document checking, so clients just
send the full document to it using the LSP notification `didChange`.

In general, you don't want to worry about execution, being this the
job of `coq-lsp`: you simply submit updated documents, and query for
the info you need. `coq-lsp` will try to get back to you ASAP.

Parts of the document are identified using positions in the text
buffer. This is much more flexible than the previous sentence-based
model.

### More on the new document engine, Flèche

In general Flèche is much more capable than the previous coq-serapi
engine, in particular you can clone documents, execute speculatively,
program your own error recovery strategies, etc... get in touch with
us if you have any questions.

### Custom calls

See [protocol documentation](doc/PROTOCOL.md) for some available
requests and methods. The common `(Query () Goals)` is now the
`proof/goals` request.

### Serialization format

`coq-lsp` used JSON by default, but the underlying serializer is the
same than we used in SerAPI. There is a very direct correspondence,
but if you need, we can provide a SEXP compatibility layer for your
needs, but often JSON produces better results due to OCaml records
being translated to JSON records.
