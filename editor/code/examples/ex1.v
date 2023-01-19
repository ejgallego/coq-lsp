(* This example showcases some features of the early server *)
Lemma addn0 n : n + 0 = n.
Proof. now induction n. Qed.

Lemma muln0 n : n * 0 = 0.
Proof. now induction n. Qed.
