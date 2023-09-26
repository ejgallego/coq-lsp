Record a := {
    proj1 : Type
  ; proj2 : Type
}.

Notation "A -> B" := (forall (_ : A), B) (at level 99, B at level 200).
Inductive foo := A | B : a -> foo.

Inductive aba := C.

Inductive eh1 := Ah1 : eh2 -> eh1
with eh2 := Bh1 : eh1 -> eh2.

Definition mu := forall (x : Type), x.

Inductive False := .

Inductive nat := O | S : nat -> nat.
Inductive bool := true | false.

Variable (j : nat).

Axiom test : False.

Fixpoint f1 (n : nat) := match n with O => true | S n => f2 n end
with f2 (n : nat) := match n with O => true | S n => f1 n end.

Class EqBar := { wit : nat }.

(* Fixme here, Instance is not recognized as a proof opener *)
Instance foobar : EqBar.
Admitted.

Section Moo.

    Variable (jj : nat).
    Hypothesis (umm : Type).

    Definition m1 := 3.

    Theorem m2 : Type. Qed.

End Moo.

Module Bar.

  Variable (u : nat).

  Parameter (v : nat).

  Definition k := 3.

  Theorem not : False. Qed.

End Bar.
