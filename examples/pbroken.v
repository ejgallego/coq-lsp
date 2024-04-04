(* See https://github.com/coq/coq/issues/12575 *)

(* If you uncomment / comment this line, the whole setup becomes broken *)
(* From Coq Require Import ssreflect. *)

Ltac CaseEq name :=
  generalize (refl_equal name); pattern name at -1 in |- *; case name.

Theorem min_or :
 forall n m : nat, min n m = n /\ n <= m \/ min n m = m /\ m < n.
Admitted.

(* Some other printing example from vscoq issue tracker *)
Universe u v.
Print Universes Subgraph (u v).