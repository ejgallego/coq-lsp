(* This example showcases some features of the early server *)
Add Rec ML Path "../_build/install/default/lib/coq/plugins/".
Add Rec LoadPath "../_build/install/default/lib/coq/theories/" as Coq.
Add Rec LoadPath "../_build/install/default/lib/coq/plugins/" as Coq.

From Coq Require Import Prelude.

Lemma addn0 n : n + 0 = n.
Proof. now induction n. Qed.

Lemma muln0 n : n * 0 = 0.
Proof. now induction n. Qed.

