(* This example showcases some features of the early server *)
From Coq Require Import Prelude.

Ltac slow := do 1000 (do 1000 idtac).
Ltac wrong := intro.

Definition j := 4.

Lemma foo n m : n + m = m + n.
Proof.
now induction n; auto; simpl; rewrite IHn; auto.
Qed.

Lemma a: True.
Proof. slow. slow. slow. slow. slow. slow. auto. Qed.

Lemma b: True.
Proof. slow. slow. wrong. auto. Qed.

Lemma c: True.
Proof. slow. slow. slow. auto. Qed.

Lemma d: True.
Proof. slow. slow. slow. auto.
Qed.
