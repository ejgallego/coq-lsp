From Coq Require Import Prelude.

Inductive paths {A : Type} (a : A) : A -> Type :=
  idpath : paths a a.

Notation "x = y :> A" := (@paths A x y) : type_scope.
Notation "x = y" := (x = y :>_) : type_scope.

Symbol Interval : Set.
Symbol i0 : Interval.
Symbol i1 : Interval.
Symbol seg : i0 = i1.

Definition transport {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y
  := match p with idpath _ => u end.


Unset Universe Polymorphism.
Symbol ap@{u v} : forall {A : Type@{u}}{B : Type@{v}} (f : A -> B) {x y : A}
  (p : x = y), f x = f y.
Rewrite Rule ap_comp :=
| @ap ?A ?P ?f _ _ (@idpath@{u} _ ?a) => @idpath ?P (?f ?a).
Symbol apD@{u v} : forall {A : Type@{u}} {P : A -> Type@{v}}
  (f : forall x, P x) {x y : A} (p : x = y), transport P p (f x) = f y.
Rewrite Rule apD_comp :=
| @apD ?A ?P ?f _ _ (@idpath _ ?a) => @idpath (?P ?a) (?f ?a).
Set Universe Polymorphism.

Symbol Interval_ind
  : forall (P : Interval -> Type)
      (a : P i0) (b : P i1) (p : transport P seg a = b),
      forall x, P x.

Symbol Interval_rec : forall (P : Type) (a b : P) (p : a = b), Interval -> P.

Rewrite Rule interval_rewrite :=
| Interval_ind ?P ?a ?b ?p i0 => ?a
| Interval_ind ?P ?a ?b ?p i1 => ?b
| apD (Interval_ind ?P ?a ?b ?p) seg => ?p
| ap (Interval_rec ?P ?a ?b ?p) seg => ?p
.

Definition funext {A : Type} {P : A -> Type} {f g : forall x, P x}
  : (forall x, f x = g x) -> f = g.
Proof.
  intros p.
  simple refine (let r := _ in _).
  1: exact (Interval -> forall x, P x).
  { intros i x; revert i.
    exact (Interval_rec _ (f x) (g x) (p x)). }
  (* Coq can't rewrite under eta :'( *)
  Fail exact (ap r seg).
Abort.
