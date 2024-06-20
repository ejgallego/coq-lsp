Lemma foo : 3 = 3.
Proof. now reflexivity. Qed.

About foo.

Reset Initial.

About foo.

Lemma foo : 2 = 2.
Proof. now reflexivity. Qed.

Lemma bar : 4 = 4.
Proof. now reflexivity. Qed.

About bar.
About foo.

Reset foo.

About foo.
About bar.

Lemma muu : 4 = 4.
Proof.
now reflexivity.
Back 2.
now reflexivity.
Qed.

Reset Initial.

About muu.
About foo.
About bar.

Lemma foo : True.
  Lemma bar : False.
  Abort All.

Lemma foo : True. now auto. Qed.

Print foo.



