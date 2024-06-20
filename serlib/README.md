## Serlib README

Welcome to `coq-serlib` README.

`coq-serlib` is a library that declares missing serialization
functions (from/to JSON, sexp), comparison, and hash functions for
most Coq datatypes, allowing users to serialize full ASTs faithfully
for example, and many other interesting use cases.

`coq-serlib` also includes support for [Coq's extensible syntax]() and
plugins.

### Builtins and Configuration

`serlib` provides some builtins and configuration values in the
`Serlib_base` and `Serlib_init` modules.

### Serializing regular Coq types

The standard recipe is to use a combination of `ppx_import` and
several ppx-based "derivers" to make `serlib` generate the
corresponding serializers.

The pattern for a Coq module `Foo` exporting the datatype `bar` and
their constructors is:

1. create a new OCaml module named `ser_foo.ml`
2. get the corresponding serializers for existing types in scope, this is unusually done in two steps:
  - serializers for OCaml Stdlib:
```ocaml
open Ppx_hash_lib.Std.Hash.Builtin
open Ppx_compare_lib.Builtin
open Sexplib.Std
```
  - serializers for types that `Foo.bar` depends on, for example:
```ocaml
module Names = Ser_names
module EConstr = Ser_eConstr
...
```
3. implement the serializers for your type. Add to `ser_foo.ml`:
```ocaml
type bar =
  [%import: Foo.bar]
  [@@deriving sexp,yojson,hash,compare]
```

Additionally, you can add an `.mli` file, with the same contents as
above, but in this case, `[@@deriving ...]` will generate the right
interface declarations.

If `Foo.bar` has no public constructors, `Obj.magic` will be
needed. `serlib` provides helpers for this, see below.

### Serializing opaque and private types

`serlib` uses `ppx_import` to retrieve the original type definitions
from Coq; when these are not available, we provide some helpers in the
`SerType` module. Current helpers are:

- `Biject`: use when it is convenient to provide an isomorphic type to
  the one that is "opaque".
- `Pierce`: use when it is not possible to access the type, you really
  want to use a copy + `Obj.magic`
- `Opaque`: when you want to declare the type as non-serializable

**note**: use of `Obj.magic` is now prohibited, all the type piercings
need to use the `Pierce` functor.

### Serializing GADTS

Unfortunately, it is not possible to easily serialize GADTS. For now,
we use a very ugly workaround: we basically copy the original Coq
datatype, in non-GADT version, then we pierce the type as their
representation is isomorphic.

We will use an example from https://github.com/coq/coq/pull/17667#issuecomment-1714473449 :

```ocaml
type _ gen_pattern = GPat : Genarg.glob_generic_argument -> [ `uninstantiated ] gen_pattern
```

In this case, we could indeed derive a serialization function (try
`[@@deriving of_sexp]` for example), however full serialization is
harder, so we may need to provide an alternative data-type:

```ocaml
module GenPatternRep : SerType.Pierceable1 = struct

    type 'a t = 'a Pattern.gen_pattern

    type _ _t = GPat of Genarg.glob_generic_argument
       [@@deriving sexp,yojson,hash,compare]
end

module GenPatternSer = SerType.Pierce1(GenPatternRep)
type 'a gen_pattern = GenPatternSer.t [@@deriving sexp,yojson,hash,compare]
```

and here you go! The main problem with this approach is that it
requires a manual check for each use of `Pierce` and each Coq
version. Fortunately the numbers of `Pierce`'s so far have been very
low.

### Pre-release checks

Due to the above, when updating SerAPI for a new release to OPAM, we
must check that the definitions we are piercing are up to date.

I perform this check with Emacs + Merlin for OCaml:

- I do `vc-git-grep` for `Pierce(` and `Pierce1(`
- For each use, I use merlin to jump to the original type
- I compare update these types

That's painful, but takes like 10 minutes, so for now it is doable a
couple of times a year. To illustrate, these are the current
occurrences to check:

```
serlib/plugins/ltac2/ser_tac2expr.ml:module T2E = Serlib.SerType.Pierce(T2ESpec)
serlib/plugins/ltac2/ser_tac2expr.ml:module GT2E = Serlib.SerType.Pierce(GT2ESpec)
serlib/ser_cooking.ml:module B_ = SerType.Pierce(CIP)
serlib/ser_environ.ml:  include SerType.Pierce(PierceSpec)
serlib/ser_float64.ml:include SerType.Pierce(PierceSpec)
serlib/ser_impargs.ml:module B_ = SerType.Pierce(ISCPierceSpec)
serlib/ser_names.ml:include SerType.Pierce(MBIdBij)
serlib/ser_names.ml:    include SerType.Pierce(PierceSpec)
serlib/ser_names.ml:  include SerType.Pierce(PierceSpec)
serlib/ser_numTok.ml:  include SerType.Pierce(PierceSpec)
serlib/ser_opaqueproof.ml:module B_ = SerType.Pierce(OP)
serlib/ser_opaqueproof.ml:module C_ = SerType.Pierce(OTSpec)
serlib/ser_rtree.ml:include SerType.Pierce1(RTreePierce)
serlib/ser_sList.ml:include SerType.Pierce1(SL)
serlib/ser_safe_typing.ml:module B_ = SerType.Pierce(PC)
serlib/ser_sorts.ml:include SerType.Pierce(PierceSpec)
serlib/ser_stateid.ml:include SerType.Pierce(SId)
serlib/ser_univ.ml:  module PierceImp = SerType.Pierce(PierceSpec)
serlib/ser_univ.ml:  include SerType.Pierce(PierceSpec)
serlib/ser_univ.ml:  include SerType.Pierce(ACPierceDef)
serlib/ser_vmemitcodes.ml:module B = SerType.Pierce(PierceToPatch)
```
