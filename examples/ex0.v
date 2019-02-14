(* This example showcases some features of the early server *)
Add Rec ML Path "../_build/install/default/lib/coq/plugins/".
Add Rec LoadPath "../_build/install/default/lib/coq/theories/" as Coq.
Add Rec LoadPath "../_build/install/default/lib/coq/plugins/" as Coq.

From Coq Require Import Prelude.
From Coq Require Import ssreflect ssrbool.
From Coq Require Import Omega.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma addn0 n : n + O = n.
Proof. by elim: n. Qed.

Lemma addnC n m : n + m = m + n.
Proof. by elim n => //= ? ->. Qed.

Lemma addnA n m l : n + m + l = m + (n + l).
Proof. by elim n => //= ? ->. Qed.

Lemma level1 : True.
  Lemma level2 : True.
  Proof. by []. Qed.
exact: level2.
Qed.

Lemma admit (T : Type) : T. Admitted.

(* Admitted leaks here XXX *)
Definition hola := 3.

Lemma broken1 : False.
Proof. Qed.

Definition adios := 3.

Lemma broken2 : False.
Proof. apply: admit. Qed.

Lemma eq0 : 0 = 0.
Proof. omega. Qed.

