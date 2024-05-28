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

Lemma failingBullet : (1 = 1) /\ (21 = 21 /\ 22 = 22) /\ (3 = 3).
Proof.
split;[|split].
- 
-
-
Qed.

Lemma failingsubProof : (1 = 1) /\ (21 = 21 /\ 22 = 22) /\ (3 = 3).
Proof.
split;[|split].
3:{ }
- idtac.
- split. 2:{ }
  + now auto.
Qed.

Lemma anotherFailing : nat * nat * nat.
Proof.
  refine (_,_,_).
  { apply S. }
  { exact 2. }
  exact 1.
Qed.

Goal Type.
Qed.

Definition baaar : Type.
Qed.

About baaar.

(* Taken from https://github.com/coq/coq/issues/18682 *)
Lemma err_bullet: Type.
_.
_
Qed.

(* Case from https://github.com/ejgallego/coq-lsp/issues/525 *)
Reset Initial.

Inductive foo := a | b | c | d | e.

Goal forall x y z w v : foo, Type.
intros [].
- intros [].
  + intros [].
    * intros [].
      -- intros [].