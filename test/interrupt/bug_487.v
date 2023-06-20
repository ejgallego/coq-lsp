(* From https://github.com/ejgallego/coq-lsp/issues/487 *)
(* Requires CompCert so that's hard to to test right now *)

Require Import Coqlib.
Require Import Integers.
Require Import Values Memory.
Require Import Cminor CminorSel.
Require Import SelectOp.

Section CMCONSTR.
Variable ge: genv.
Variable sp: val.
Variable e: env.
Variable m: mem.

Definition unary_constructor_sound (cstr: expr -> expr) (sem: val -> val) : Prop :=
  forall le a x,
  eval_expr ge sp e m le a x ->
  exists v, eval_expr ge sp e m le (cstr a) v /\\ Val.lessdef (sem x) v.

Lemma eval_mulimm_base:
  forall n, unary_constructor_sound (mulimm_base n) (fun x => Val.mul x (Vint n)).
induction n.
econstructor.
unfold mulimm_base.
unfold Int.one_bits.
unfold map.
simpl.
