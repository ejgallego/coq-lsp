Record t : Type := {
  carrier :> Type;
  unit : carrier;
  mult : carrier -> carrier -> carrier;
  assoc : forall a b c, mult a (mult b c) = mult (mult a b) c;
  unit_l : forall a, mult unit a = a;
  unit_r : forall a, mult a unit = a;
}.

Print t.

Module A.
Axiom A : Type.
Axiom B : Type.
Axiom C : Type.
Axiom D : Type.
Axiom E : Type.
End A.

Print A.

Goal True /\ True /\ True /\ True /\ True /\ True /\ True /\ True /\ True /\ True /\ True.
apply I.
Qed.
