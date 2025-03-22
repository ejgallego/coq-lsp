(* From WaterProof *)

Require Import Ltac2.Ltac2.
Require Import Ltac2.Message.

Require Import Waterproof.Waterproof.
Require Import Waterproof.Automation.
Require Import Waterproof.Tactics.
Require Import Waterproof.Util.Assertions.

(** Test 0: works with existence statement*)
Goal (exists n : nat, n + 1 = n)%nat -> False.
Proof.
  intro H.
  Obtain such an n.
Abort.

(* -------------------------------------------------------------------------- *)
(** * Testcases for [It suffices to show that ...] 
  Variant without the [by] clause.
*)

Open Scope nat_scope.

(** * Test 1
    Base case: give a statement that indeed suffices.
*)
Lemma test_it_suffices_1: forall x:nat, x>0 /\ x < 2 -> x = S (0).
Proof.
  intros x.
  It suffices to show that (x = 1).
  (* Old goal should have been proven by the above,
    now the assumption used remains to be proven.*)
  assert_goal_is constr:(x=1).
Abort.

(** * Test 2
    Error case: give a statement does not suffice to complete the proof.
*)
Lemma test_it_suffices_2: forall A B : Prop , A /\ A -> B.
Proof.
  intros A B.
  (* Clearly this statement isn't helpful in proving the goal! *)
  let result () := By (f_increasing) it suffices to show that (1 + 1 = 2) in
  assert_raises_error result.
Abort.

(** Test 0: This should work *)
Goal forall n : nat, ( ( (n = n) /\ (n + 1 = n + 1) ) -> (n + 1 = n + 1)).
    intro n.
    intro i.
    Because (i) both (n = n) and (n + 1 = n + 1) hold.
Abort.

(** Test 1: This should work, test first prop labeled. *)
Goal forall n : nat, ( ( (n = n) /\ (n + 1 = n + 1) ) -> (n + 1 = n + 1)).
    intro n.
    intro i.
    Because (i) both (n = n) (ii) and (n + 1 = n + 1).
Abort.
