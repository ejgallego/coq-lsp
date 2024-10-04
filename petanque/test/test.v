From Coq Require Import List.
Import ListNotations.

Lemma rev_snoc_cons A :
  forall (x : A) (l : list A), rev (l ++ [x]) = x :: rev l.
Proof.
  induction l.
  - reflexivity.
  - simpl. rewrite IHl. simpl. reflexivity.
Qed.

(* This is for testing proof finished *)
Lemma deepBullet : (1 = 1) /\ (21 = 21 /\ 22 = 22).
Proof.
split.
- now reflexivity.
- split.
  + now reflexivity.
  + now reflexivity.
Qed.
