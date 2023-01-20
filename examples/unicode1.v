Axiom P : nat -> Prop.
Axiom foo : forall {n}, P (S n) -> P n.
Ltac foo := apply foo.
Infix "⊆" := lt (at level 10).

Goal forall Γ Δ, Γ ⊆ Δ -> P Γ.
(* check goal is updated after the intros here properly *)
intros Γ Δ s.
foo.
