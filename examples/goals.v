Lemma foo (a b: nat): (1 = 1) /\ (21 = 21 /\ 22 = 22) /\ (3 = 3).
Proof.
pose (n := 3).
split;[|split].
- now reflexivity.
- split.
  + shelve.
  + now admit.
- now reflexivity.
Qed.

Lemma bar : nat.
Proof.
pose (a := 3).
exact a.
Qed.