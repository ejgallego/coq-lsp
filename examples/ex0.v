(* This example showcases some features of the early server *)
From Coq Require Import ssreflect ssrbool.
From Coq Require Import Lia.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma addn0 n : n + O = n.
Proof. by elim: n. Qed.

Definition m := addn0.

Print m.

Definition a := 2.

Lemma addnC n m : n + m = m + n.
Proof. by elim: n => //= ? ->. Qed.

Lemma addnAC n m l : n + m + l = m + (n + l).
Proof.
  by elim : n => //= ? ->.
Qed.

Lemma level1 : True.
  Lemma level2 : True.
  Proof. by []. Qed.
exact: level2.
Qed.

Lemma admit (T : Type) : T. Admitted.

(* Admitted leaks here XXX *)
Definition hola := 3.

Inductive event : Type :=
  | R of nat
  | S of nat. 

Record pair_emilio := {
  fst : nat;
  snd : nat
}.

Inductive pair' := Pair of nat & nat.

Definition fst' (x : pair') := match x with
 | Pair x _ => x
end.

Definition snd' (x : pair') := match x with
 | Pair _ y => y
end.

Lemma foo n m : n + m = m + n.
Proof.
Qed.

(* Church enconding *)

Definition pair'' (A B : Type) :=
 forall C, A -> B -> (A -> B -> C).

Variables (x y : Type).

Lemma foo : x = x.
Proof. by []. Qed.

Record network := 
 { time : Type
 ; address : Type
 ; payload : Type
 ; send : time -> address -> time -> bool
 }.

Lemma broken1 : False.
Proof. admit.
Qed.

Definition adios := 9.

Lemma broken2 : False.
Proof. apply: admit. Qed.

Lemma eq0 : 0 = 0.
Proof. by []. Qed.

Lemma eqN (n m : nat) : n = n.
Proof.
by [].
Qed.

Section Foo.

Lemma addnA m n p : m + n + p = m + (n + p).
Proof. by elim: m n p => //= m IHn n p; rewrite IHn. Qed.

Lemma foobar (n : nat) : n = n.
Proof. by []. Qed.

Definition muu := 3.

(* End Foo. *)