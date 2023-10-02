Require Import ZArith.

Open Scope Z.

Goal 2^17000 <> 0.
Time cbv.
(* This computes in a few ms, but display takes 15s in CoqIDE and VSCoq *)
congruence.
Qed.

Definition hideZ {z : Z} := z.
Opaque hideZ.

Goal @hideZ (2^17000) <> 0.
Time cbv.
(* This computes in a few ms and displays immediately in CoqIDE and VSCoq if implicit arguments are off *)
Abort.
