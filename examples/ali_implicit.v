From Coq Require Import Prelude.

Unset Printing Notations.

(* Observe what happens on hover after Arguments: *)

Axiom T1 : forall A B C D, A * B * C * D.
Arguments T1 {A} B {C} D.
(* T1: forall {A : Type} (B : Type) {C : Type} (D : Type),
prod (prod (prod A B) C) D *)

Class T2 (A B C D : Type) := {}.
Arguments T2 {A} B {C} D.
(* T2 (A B C D : Type) : Prop *)
About T2.
Record T3 (A B C D : Type) := {}.
Arguments T3 {A} B {C} D.
(* T3 (A B C D : Type) : Prop *)
About T3.
Definition T4 (A B C D : Type) := (fun a b c d => True) A B C D.
Arguments T4 {A} B {C} D.
(* T4: forall {_ : Type} (_ : Type) {_ : Type} (_ : Type), Prop *)
About T4.
Definition T5 (A B C D : Type) : Type. Proof. exact ((fun a b c d => True) A B C D). Qed.
Arguments T5 {A} B {C} D.
(* T5: forall {_ : Type} (_ : Type) {_ : Type} (_ : Type), Type *)
About T5.
Inductive T6 (A B C D : Type) : Type := .
Arguments T6 {A} B {C} D.
(* T6 (A B C D : Type) : Type *)

CoInductive T7 (A B C D : Type) : Type := {}.
Arguments T7 {A} B {C} D.
(* T7 (A B C D : Type) : Type *)