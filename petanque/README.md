_Petanque_ (pronounced "petanque") is a
[gymnasium](https://gymnasium.farama.org/)-like environment for the
Coq Proof Assistant.

_Petanque_ is geared towards use cases where interacting at the
document-level (like Flèche provides) in not enough, usually because
we want to work on purely proof-search level vs the document level
one.

Petanque follows the methodology developed in SerAPI, thus we specify
an OCaml API (`agent.mli`) which is then exposed via some form of RPC.

## Authors

- Guilaume Baudart (Inria)
- Emilio J. Gallego Arias (Inria)
- Laetitia Teodorescu (Inria)

## Acknowledgments

- Andrei Kozyrev
- Alex Sánchez-Stern

## Install instructions

Please see the regular `coq-lsp` install instructions. In general you
have three options:

- use a released version from Opam
- use a development version directly from the tree
- install a development version using Opam

See the contributing guide for instructions on how to perform the last
two.

## Using `petanque`

You can use `petanque` in 2 different ways:

- call the API directly from your OCaml program
- use the provided `pet` JSON-RPC shell

to execute the `pet` JSON-RPC shell do:
```
make
dune exec -- rlwrap %{bin:pet}
```

`rlwrap` is just a convenience, if your dune version is too old and
don't recognize the `%{bin:pet}` form, you can just do `dune exec -- pet`.

### Petanque options

Petanque can be initalized from the command line by passing the `--root` parameter to it:
```
make
dune exec -- rlwrap %{bin:pet} --root=/absolute/path/to/my/project
```

NOTE: If you use this option, you should not call `Init`!

### A first example:

Please use one line per json input. json input examples are:
```json
["Init",{"debug": false,"root":"file:///home/egallego/research/coq-lsp/examples/"}]
["Init",["Ok",1]]

["Start",{"env":1,"uri": "file:///home/egallego/research/coq-lsp/examples/ex0.v","thm":"addnC"}]
["Start",["Ok",1]]

["Run_tac", {"st": 1, "tac": "induction n."}]
["Run_tac", ["Ok", 2]]

["Run_tac", {"st": 2, "tac": "simpl."}]
["Run_tac", 3]

["Run_tac", {"st": 3, "tac": "auto."}]
["Run_tac",4]

["Premises", {"st": 2}]
["Premises", ...]
```

Seems to work! (TM) (Famous last words)

