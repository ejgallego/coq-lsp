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

To use `petanque`, you need to some form of shell, or you can just
call the API directly from your OCaml program.
