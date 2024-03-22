_Petanque_ (pronounced "petanque") is a gym-like environment for the
Coq Proof Assistant.

_Petanque_ is geared towards use cases where interacting at the
document-level (like Flèche provides) in not enough

## Authors

- Guilaume Baudart (Inria)
- Emilio J. Gallego Arias (Inria)
- Laetitia Teodorescu (Inria)

## Acknowlements

- Alex-Sánchez Stern

## Install instructions

Once in a `coq-lsp` dev environment, you need

Then do the `ocaml-in-python` setup:

```
You should register the "ocaml" package in your Python environment.
   There are two options:

     (1) either you register the package with "pip" using the following
         command:
           pip install --editable "/home/egallego/.opam/dev-coq-lsp/lib/ocaml-in-python"

     (2) or you add the following definition to your environment:
           export PYTHONPATH="/home/egallego/.opam/dev-coq-lsp/share/python/:$PYTHONPATH"
```

## Running `pet shell`

Only once, setup the coq-lsp build environment (if you haven't already):
```
opam install --deps-only .
make submodules-init
```

to build and execute `petanque` do:
```
make
dune exec -- rlwrap %{bin:pet}
```

`rlwrap` is just a convenience, if your dune version is too old and
don't recognize the `%{bin:pet}` form, you can just do `dune exec -- pet`.

### A first example:

Please use one line per json input. json input examples are:
```json
["Start",{"uri":"file:///home/egallego/research/coq-lsp/examples/ex0.v","thm":"addnC"}]
["Start",131266756246311]

["Run_tac", {"st": 131266756246311, "tac": "induction n."}]
["Run_tac",131266894677423]

["Run_tac", {"st": 131266894677423, "tac": "simpl."}]
["Run_tac",131266896660087]

["Run_tac", {"st": 131266896660087, "tac": "auto."}]
["Run_tac",131266896448871]
```

Seems to work! (TM) (Famous last words)

## Running (not yet working ocaml-in-python)

```
make && PYTHONPATH="/home/egallego/.opam/dev-coq-lsp/share/python/:$PYTHONPATH" dune exec -- python3
```

then in the Python shell:
```
import ocaml
ocaml.require("coq-lsp.petanque")

from ocaml import Petanque

Petanque.Agent.start()
```
