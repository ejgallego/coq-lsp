(* Test for #886. *)
Lemma foo n m : n ++ m = n.
Qed.

From Coq Require Import List.
Import ListNotations.

(* To test for search and feedbacks *)
Inductive naat := OO.
Lemma i_want_to_be_searched : naat.
Proof. apply OO. Qed.

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
