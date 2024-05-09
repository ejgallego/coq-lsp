(*
  Test file for #150, provided by Clement Pit-Claudel.

  Note that the problem here is with serialization of Goals, not AST.
 *)

Require Export NumPrelude NZAxioms.
Require Import NZBase NZOrder NZAddOrder.

(** In this file, we investigate the shape of domains satisfying
    the [NZDomainSig] interface. In particular, we define a
    translation from Peano numbers [nat] into NZ.
*)

Local Notation "f ^ n" := (fun x => nat_rect _ x (fun _ => f) n).

#[global] Instance nat_rect_wd n {A} (R:relation A) :
 Proper (R==>(R==>R)==>R) (fun x f => nat_rect (fun _ => _) x (fun _ => f) n).
Proof.
intros x y eq_xy f g eq_fg; induction n; [assumption | now apply eq_fg].
Qed.

Module NZDomainProp (Import NZ:NZDomainSig').
Include NZBaseProp NZ.

(** * Relationship between points thanks to [succ] and [pred]. *)

(** For any two points, one is an iterated successor of the other. *)

Lemma itersucc_or_itersucc n m : exists k, n == (S^k) m \/ m == (S^k) n.
Proof.
revert n.
apply central_induction with (z:=m).
 { intros x y eq_xy; apply ex_iff_morphism.
  intros n; apply or_iff_morphism.
 + split; intros; etransitivity; try eassumption; now symmetry.
 + split; intros; (etransitivity; [eassumption|]); [|symmetry];
    (eapply nat_rect_wd; [eassumption|apply succ_wd]).
 }
exists 0%nat. now left.
intros n. split; intros [k [L|R]].
exists (Datatypes.S k). left. now apply succ_wd.
destruct k as [|k].
simpl in R. exists 1%nat. left. now apply succ_wd.
rewrite nat_rect_succ_r in R. exists k. now right.
destruct k as [|k]; simpl in L.
exists 1%nat. now right.
apply succ_inj in L. exists k. now left.
exists (Datatypes.S k). right. now rewrite nat_rect_succ_r.
Qed.

End NZDomainProp.
