# coq-lsp / Flèche plugins

Easiest way to use plugins is

```
$ fcc --root=dir --plugin=coq-lsp.plugin.$name file.v
```

- `example`: prints a "this file was checked" message
- `astdump`: dumps the Ast of the document, in both sexp and JSON
  formats
- `goaldump`: dumps the Ast of the document in JSON format, along with
  the goals at that state.
