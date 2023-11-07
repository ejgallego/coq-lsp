(* Thanks to Pierre Courtieu for the example and report *)
Require Import Utf8.

(* Check hover works properly for `Nopick` *)
Variant pick_spec (T : Type) (P : T -> Prop) : option T -> Type :=
  | Pick : forall x : T, P x -> pick_spec T P (Some x)
  | Nopick : (∀ x : T, ¬ (P x)) → pick_spec T P None.
