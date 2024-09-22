(* test for  *)

Symbols
  (pplus : nat -> nat -> nat)
  (pmul : nat -> nat -> nat).

Notation "a ++ b" := (pplus a b).
Notation "a ** b" := (pmul a b) (at level 30).

Rewrite Rules pplus_rewrite :=
| ?n ++ 0 => ?n
| ?n ++ S ?m => S (?n ++ ?m)
| 0 ++ ?n => ?n
| S ?n ++ ?m => S (?n ++ ?m)
| ?n ++ (?m ++ ?o) => (?n ++ ?m) ++ ?o.

Rewrite Rules pmul_rewrite :=
| 0 ** ?n => 0
| ?n ** 0 => 0
| S ?n ** ?m => ?n ++ (?n ** ?m)
| ?n ** S ?m => ?m ++ (?n ** ?m)
| ?n ** (?m ** ?o) => (?n ** ?m) ** ?o.

Lemma foo n m : S n ** m ++ 0 = n ++ (n ** m).
Proof. now reflexivity. Qed.

