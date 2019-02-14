(* This example showcases some features of the early server *)
Add Rec ML Path "../_build/install/default/lib/coq/plugins/".
Add Rec LoadPath "../_build/install/default/lib/coq/theories/" as Coq.
Add Rec LoadPath "../_build/install/default/lib/coq/plugins/" as Coq.

From Coq Require Import Prelude.

Ltac slow := do 100 (do 100 idtac).
Ltac wrong := intro.

Lemma a: True.
Proof. slow. slow. slow. slow. slow. slow. auto. Qed.

Lemma b: True.
Proof. slow. slow. wrong. auto. Qed.

Lemma c: True.
Proof. slow. slow. slow. auto. Qed.

Lemma d: True.
Proof. slow. slow. slow. auto.
Qed.
