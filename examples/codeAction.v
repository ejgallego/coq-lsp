(* Example codeAction, from Coq's test suite *)

Module M. Definition y := 4. End M.
Import M.

#[deprecated(use=y)]
Definition x := 3.

Module N. Definition y := 5. End N.
Import N.

Definition d1 := x = 3.

Module M1.
Notation w := x.
End M1.
Import M1.

#[deprecated(use=w)]
Notation v := 3.

Module M2.
Notation w := 5.
End M2.
Import M2.

Definition d2 := v = 3.

Fail #[deprecated(use=w)]
Notation "a +++ b" := (a + b) (at level 2).

Fail #[deprecated(use=nonexisting)]
Definition y := 2.

(***********************************************)
Module A.
End B.

(***********************************************)
Require Import Extraction.

Module nat. End nat.

Extraction nat.
