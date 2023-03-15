(** Test case highlithing .vo storing locs by Dan Christensen, see
 https://github.com/coq/coq/issues/17312 *)

Ltac bar := auto.

Tactic Notation "foo" := auto.

#[export] Hint Extern 0 (_ = _) => idtac : typeclass_instances.
