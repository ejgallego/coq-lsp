(* From https://github.com/ejgallego/coq-lsp/issues/484 *)
From Coq Require Import Prelude.

Axiom Loop : Type.
Existing Class Loop.

Axiom loop : Loop -> Loop.
#[export] Existing Instance loop.

Global Instance foo : Loop.
Proof. Admitted.

Goal Loop.
exact _.

(* Try commenting out foo and TC search will loop *)
