From Coq Require Import ssreflect ssrbool ssrfun.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Equality.

Definition axiom T (e : rel T) := forall x y, reflect (x = y) (e x y).

Structure mixin_of T := Mixin {op : rel T; _ : axiom op}.
Notation class_of := mixin_of (only parsing).

Section ClassDef.

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).

Definition class := let: @Pack _ c := cT return class_of cT in c.

Definition clone := fun c & cT -> T & phant_id (@Pack T c) cT => Pack c.

End ClassDef.

Definition eqType := Equality.type.
Coercion Equality.sort : Equality.type >-> Sortclass.
Notation EqType T m := (@Equality.Pack T m).

Module Ordered.

Section RawMixin.

Structure mixin_of (T : eqType) :=
  Mixin {ordering : rel T;
         _ : irreflexive ordering;
         _ : transitive ordering;
        }.
End RawMixin.

Section ClassDef.

Record class_of (T : Type) := Class {
   base : Equality.class_of T;
   mixin : mixin_of (Equality.Pack base)}.

Local Coercion base : class_of >-> Equality.class_of.

Structure type : Type := Pack {sort : Type; _ : class_of sort;}.
Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (cT : type).
Definition class := let: @Pack _ c as cT' := cT return class_of cT' in c.

Definition pack b (m0 : mixin_of (EqType T b)) :=
  fun m & phant_id m0 m => Pack (@Class T b m).

Definition eqType := Equality.Pack class.

End ClassDef.

Module Exports.
Coercion eqType : type >-> Equality.type.
Canonical Structure eqType.
Notation ordType := Ordered.type.
Definition ord T : rel (sort T) := (ordering (mixin (class T))).
End Exports.
End Ordered.
Export Ordered.Exports.

Definition eq_op T := Equality.op (Equality.class T).

Notation "x == y" := (eq_op x y)
  (at level 70, no associativity) : bool_scope.

Lemma eqP T : Equality.axiom (@eq_op T).
Proof. by case: T => ? []. Qed.
Arguments eqP {T x y}.

Definition oleq (T : ordType) (t1 t2 : T) := ord t1 t2 || (t1 == t2).

Prenex Implicits ord oleq.

Section Lemmas.
Variable T : ordType.
Implicit Types x y : T.

Variable trans : transitive (@ord T).

Lemma otrans : transitive (@oleq T).
Proof.
move=>x y z /=.
case/orP; last by move/eqP=>->.
rewrite /oleq; move=>T1.
case/orP; first by move/(trans T1)=>->.
by move/eqP=><-; rewrite T1.
Qed.

End Lemmas.
