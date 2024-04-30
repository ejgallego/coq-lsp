Set Primitive Projections.

CoInductive t : Set := mk { pred : option t }.

CoInductive equal : t -> t -> Prop  :=
| equal_zero : equal (mk None) (mk None)
| equal_succ x y : equal x y -> equal (mk (Some x)) (mk (Some y)).

Lemma equal_refl : forall x, equal x x.
Proof.
	cofix cih.
	intros x.
	destruct (pred x) as [x' | ] eqn:eq; auto.
	(* correct error reported *)
	
    Guarded.
	(* correct error reported *)
	Defined.
    (* But switching to Qed. crashes everything instead of reporting the error *)
Qed.
