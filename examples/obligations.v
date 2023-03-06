(** Test case for obligations display. *)

From Coq Require Import Program.
From Coq Require Import Program.Tactics.

Program Definition Ob : _ := _.
Next Obligation.
exact nat. Defined.
Next Obligation.
unfold Ob_obligation_1.
exact 3. Defined.

Eval compute in Ob.
