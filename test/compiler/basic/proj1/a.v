From Coq Require Reals.

Definition aa := 3.

Lemma foo : True.
Proof. 
(* Some comment *)
auto .
Qed.

Optimize Heap.