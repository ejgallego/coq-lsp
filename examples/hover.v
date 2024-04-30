(* Bug from https://github.com/coq-community/vscoq/issues/731 *)
Definition Xᵒ : nat := 0.

Definition Y : nat := 1.

(* In the following, we gives feedback about Y but not Xᵒ *)
Goal Y + Xᵒ = 1.