# Instruction for customising coq-lsp

## Install good version

Create a new switch:

```bash
opam switch create custom_coq_lsp 5.1.0
opam switch custom_coq_lsp
```

Install coq/rocq dependencies:

```bash
opam pin add rocq-runtime https://github.com/coq/coq.git#7d4ec9ecfef45f6536d144b3d7919e4129d73274
opam pin add rocq-core https://github.com/coq/coq.git#7d4ec9ecfef45f6536d144b3d7919e4129d73274
opam pin add rocq-stdlib https://github.com/coq/stdlib.git#155be26dc10a8b6ddb3cfbdd4c144c077c583b5f
opam pin add rocq https://github.com/coq/coq.git#7d4ec9ecfef45f6536d144b3d7919e4129d73274
opam pin add coq-core https://github.com/coq/coq.git#7d4ec9ecfef45f6536d144b3d7919e4129d73274
opam pin add coq-stdlib https://github.com/coq/stdlib.git#155be26dc10a8b6ddb3cfbdd4c144c077c583b5f
opam pin add coqide-server https://github.com/coq/coq.git#7d4ec9ecfef45f6536d144b3d7919e4129d73274
opam pin add coq https://github.com/coq/coq.git#7d4ec9ecfef45f6536d144b3d7919e4129d73274
```

Install dependencies for petanque:

```bash
opam install lwt logs
```

Install coq-lsp:

```bash
opam pin coq-lsp https://github.com/LLM4Rocq/coq-lsp.git#MorePetanqueCommands
```

## New petanque operation

Write the code in [agent.ml](./petanque/agent.ml) and [agent.mli](./petanque/agent.mli),
next you have to add the support for it in:
[protocol.ml](./petanque/json/protocol.ml),
[interp.ml](./petanque/json/interp.ml),
[client.ml](./petanque/json_shell/client.ml) and [client.mli](./petanque/json_shell/client.mli).

## Use your modifications

Once you have done your modifications, simply push your changes to the repository and reload coq-lsp:

```bash
opam upgrade coq-lsp
```
