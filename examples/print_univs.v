From Coq Require Import Prelude.
Set Printing Universes.
Set Universe Polymorphism.

Definition arr (S: Type) : Type := S.

Print arr.

Inductive foo (M : Type) : Type -> Type :=
    bar : M -> Type -> foo M nat.

Print foo.

About foo.
