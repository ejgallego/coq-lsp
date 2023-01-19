(* This example showcases some features of the early server *)
From Coq Require Import Prelude.

Ltac slow := do 100 (do 100 idtac).
Ltac wrong := intro.

Definition j := 3.

Lemma a: True.
Proof. slow. slow. slow. slow. slow. slow. auto. Qed.

Lemma b: True.
Proof. slow. slow. wrong. auto. Qed.

Lemma c: True.
Proof. slow. slow. slow. auto. Qed.

Lemma d: True.
Proof. slow. slow. slow. auto.
Qed.
