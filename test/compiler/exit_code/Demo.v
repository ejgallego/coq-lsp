Theorem add_0_r (n : nat) : n + 0 = n.
Proof.
  induction n as [| n' IHn'].
  -  (* n = 0 *)
     now reflexivity.
  -  (* n = S n' *) simpl.
     rewrite -> IHn'.
     now reflexivity.
Qed.

(* Error 1 *)
Theorem add_0_r (n : nat) : n + 0 = n.
(* Error 2 *)
Qed.
