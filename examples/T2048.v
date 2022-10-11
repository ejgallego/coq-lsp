Require Import Ascii String List EqNat NArith.

Open Scope string_scope.
Open Scope N_scope.

(******************************************************************************)
(*                                                                            *)
(*           A  Coq version of the 2048 game                                  *)
(*                                          Laurent.Thery@inria.fr            *)
(*                                                                            *)
(******************************************************************************)

(* Possible moves *)
Inductive move := Rm (* right *) | Lm (* left *) | Um (* up *) | Dm (* down *).

(* Remove all the elements a of l such that p a holds *)
Fixpoint strip {A : Type} (p : A -> bool) l := 
      match l with
      | nil => l
      | a :: l1 => if p a then strip p l1 else a :: strip p l1
      end.

(* Cumulative action on a line *)
Fixpoint cumul (n : nat) (l : list N) {struct n} : list N :=
  match n with
  | 0%nat => nil | 1%nat => hd 0 l :: nil
  | S (S _ as n1) =>
      let a := hd 0 l in
      let l1 := tl l in
      let b := hd 0 l1 in
          if a =? b then (a + b) :: cumul n1 (tl l1)
          else a :: cumul n1 l1
  end.

(* Cumulative action + strip on lines *)
Definition icumul n := map (fun x => cumul n (strip (N.eqb 0) x)).

(* Count the number of occurrences of p on a line *)
Definition count (p : N -> bool) :=
  fold_right (fun n => if p n then N.succ else id) 0.

(* Count the number of occurrences of p on lines *)
Definition icount p := fold_right (fun l => N.add (count p l)) 0%N.

(* Check if v occurs in the lines *)
Definition is_won v ll := negb ((icount (N.eqb v) ll) =? 0).

(* Count the number of zeros in the lines *)
Definition zeros := icount (N.eqb 0).

(* Replace the n th occurrence of p with v in ligne l *)
Fixpoint replace n (p : N -> bool) (v : N) l  :=
  match l with 
  | a :: l1 => if p a then
                 if n =? 0 then v :: l1
                 else a :: replace (n - 1) p v l1
              else a :: replace n p v l1
  | nil => nil
  end.

(* Replace the n th occurrence of p with v in lignes ll *)
Fixpoint ireplace n (p : N -> bool) v ll  :=
  match ll with 
  | l :: ll1 => let m := count p l in
    if n <? m then (replace n p v l) :: ll1
    else l :: ireplace (n - m) p v ll1
  | nil => nil
end.

(* Flip the board *)
Definition iflip (n : nat) := map (@rev N).

(* Rotate the board *)
Fixpoint irotate (n : nat) ll := 
  match n with
  | O    => nil
  | S n1 =>  map (hd 0%N) ll :: irotate n1 (map (@tl _) ll) 
  end.

(* Iterator *)
Fixpoint iter {A : Type} n (f : A -> A) a  :=
  match n with O => a | S n1 => f (iter n1 f a) end.

(* Make Empty board *)
Definition make_board n :=
  let l := iter n (cons 0) nil in iter n (cons l) nil.
 
(* Apply a test on a list *)
Fixpoint test_list {A: Type} (f : A -> A -> bool) l1 l2 :=
  match l1, l2 with
  | nil, nil => true
  | a :: l3, b :: l4 => if f a b then test_list f l3 l4 else false
  | _, _ => false
  end.

(* Equal boards *)
Definition eq_board := test_list (test_list N.eqb).

(* Make a move *)
Definition make_move n move b :=
   match move with
  | Lm => icumul n b 
  | Rm => iflip n (icumul n (iflip n b))
  | Um => irotate n (icumul n (irotate n b))
  | Dm => irotate n (iflip n (icumul n (iflip n (irotate n b))))
  end.

(* Fast mod like *)
Definition mmod m n :=
  let l := N.log2 n in
  let mask := N.shiftl 1 (l + 1) - 1 in
  let v := N.land mask m in
  v mod n.

(* Fast div like *)
Definition mdiv m n :=
  let l := N.log2 n in
  N.shiftr m (l + 1).

(* Add a number from gl inside b *)
Definition add_val s (gl : list N) b := 
      let z := zeros b in
      if z =? 0 then None else
      (* Which empty cell gets the new number *)
      let k := mmod s z in
      let s1 := mdiv s z in
      (* Which value to put in the empty cell *)
      let le := N.of_nat (length gl) in
      let v1 := nth (N.to_nat (mmod s1 le)) gl 0 in
      let s2 := mdiv s1 le in
      let b1 := ireplace k (N.eqb 0) v1 b in
      Some (s2, b1).

(* Encoding of the result *)
Definition Invalid_Move := False.
Definition Lost := False.
Definition Won (t : list move) := True.

(* Printing Stuff *)

Definition nl := (String (ascii_of_nat 10) "")%string.

(* Number of digits of a number *)

Fixpoint digit_aux m n :=
  if n =? 0 then 0
  else
  match m with 0%nat => 0 | S m1 => digit_aux m1 (n / 10) + 1
  end.

Definition digit n := N.to_nat (digit_aux (N.to_nat (N.log2 n)) n).

(* Digit to ascii *)
Definition d2a d := ascii_of_N (48 + d).

(* Number to string *)
Fixpoint n2s n m :=
  match n with 0%nat => ""%string | S n1 =>
  if m =? 0 then
     iter n (fun l => " " ++ l)%string ""%string
  else
    ((n2s n1 (m / 10)%N) ++ (String (d2a (m mod 10)%N) ""))%string
  end.

(* Line to string *)
Definition l2s n l :=
  (fold_right (fun r s => "|" ++ n2s n r ++ s) ("|" ++ nl) l)%string.

(* Make a line *)
Definition make_line n :=
    iter n (fun l => "-" ++ l)%string nl.
 
(* Board to string *)
Definition b2s n m l :=
  let li := make_line ((m + 1) * n + 1)  in
  (nl ++ fold_right (fun r s => li ++ l2s n r ++ s) li l)%string.

(* Possible result after a game *)
Inductive result := 
  iresult (*invalid *) | lresult (* lost *) |  wresult (* win *) |
  vresult (_ : N) (_ : list (list N)) (* valid *).

(* Compute the next board *)
Definition next_board n s gl v m b :=
    let b1 := make_move n m b in
    if eq_board b b1 then iresult
    else 
      if is_won v b1 then wresult else
      let z := zeros b1 in
      if z =? 0 then lresult else
      match add_val s gl b1 with
      | None => lresult
      | Some (s2, b2)  => vresult s2 b2
      end.

(* Apply the list of moves ms to a position b *)
Fixpoint games n d s gl v ms b st :=
  match ms with
  | m :: ms1 =>
    let nb := next_board n s gl v m b in
    match nb with
    | iresult => Invalid_Move
    | lresult => Lost 
    | wresult => Won ms1
    | vresult s1 b1 =>
          games n d s1 gl v ms1 b1 (b2s d n b1)
    end
  | _ => Lost
  end.

Lemma gamesE n d s gl v m ms1 b st :
games n d s gl v (m :: ms1) b st =
    let nb := next_board n s gl v m b in
    match nb with
    | iresult => Invalid_Move
    | lresult => Lost 
    | wresult => Won ms1
    | vresult s1 b1 =>
          games n d s1 gl v ms1 b1 (b2s d n b1)
    end.
Proof. trivial. Qed.

Definition start_game n s gl v ms b :=
      match add_val s gl b with
      | None => Lost
      | Some (s1, b1) =>
          let d := digit v in 
          games n d s1 gl v ms b1 (b2s d n b1)
      end.

Definition new_game n s gl v ms :=
  start_game n s gl v ms (make_board n).

(* Start a new games with empty board *)
Definition g2048 s :=
  new_game 4 s (2 :: 4 :: nil) 2048.


(* Start a new games with a given board *)
Definition s2048 s :=
  start_game 4 s (2 :: 4 :: nil) 2048.

(* Compute the string version of the board *)
Ltac bsimpl :=
  try match goal with
  |- context[b2s ?X1 ?X2 ?X3] =>
     let v := eval vm_compute in (b2s X1 X2 X3) in
     replace (b2s X1 X2 X3) with v; [idtac | vm_compute; apply refl_equal]
  end.

(* Simplifications lemmas *)
Lemma gamesE1 n d s gl v m ms1 b st :
  next_board n s gl v m b = iresult ->
  games n d s gl v (m :: ms1) b st = Invalid_Move.
Proof.
intros H; simpl; rewrite H; auto.
Qed.

Lemma gamesE2 n d s gl v m ms1 b st :
  next_board n s gl v m b = lresult ->
  games n d s gl v (m :: ms1) b st = Lost.
Proof.
intros H; simpl; rewrite H; auto.
Qed.

Lemma gamesE3 n d s gl v m ms1 b st :
  next_board n s gl v m b = wresult ->
  games n d s gl v (m :: ms1) b st = Won ms1.
Proof.
intros H; simpl; rewrite H; auto.
Qed.

Lemma gamesE4 s1 b1 n d s gl v m ms1 b st :
  next_board n s gl v m b = vresult s1 b1 ->
  games n d s1 gl v ms1 b1 (b2s d n b1) -> games n d s gl v (m :: ms1) b st.
Proof.
intros H; simpl; rewrite H; auto.
Qed.

(* Compute the next board  *)
Ltac nsimpl :=
match goal with
|- games ?X1 ?X2 ?X3 ?X4 ?X5 (?X6 :: _) ?X7 ?X8 =>
   let v := eval vm_compute in (next_board X1 X3 X4 X5 X6 X7) in
    (match v with
    | iresult => rewrite gamesE1; [idtac | vm_compute; apply refl_equal]
    | lresult => rewrite gamesE2; [idtac | vm_compute; apply refl_equal]
    | wresult => rewrite gamesE3; [idtac | vm_compute; apply refl_equal]
    | vresult ?s1 ?b1 => apply (gamesE4 s1 b1); [vm_compute; apply refl_equal | idtac]
end ) end.

(* Generic tactic for move *)
Ltac gen_tac v := 
  match goal with
  |- games ?X1 ?X2 ?X3 ?X4 ?X5 ?X6 ?X7 ?X8 => 
       refine (_ : games X1 X2 X3 X4 X5 (v :: _) X7 X8)
  end.

(* Four tactic for the moves *)
Ltac R := gen_tac Rm; nsimpl; bsimpl.
Ltac L := gen_tac Lm; nsimpl; bsimpl.
Ltac U := gen_tac Um; nsimpl; bsimpl.
Ltac D := gen_tac Dm; nsimpl; bsimpl.

(* Four tactic for the moves fast version : no printing *)
Ltac Rf := gen_tac Rm; nsimpl.
Ltac Lf := gen_tac Lm; nsimpl.
Ltac Uf := gen_tac Um; nsimpl.
Ltac Df := gen_tac Dm; nsimpl.

(* Start tactic *)
Ltac S := eexists; do 3 red; simpl;
  try (set (x := b2s _ _ _); vm_compute in x; unfold x; clear x).
(* Final tactic *)
Ltac F := refine (_ : Won nil); apply I.

Fixpoint lrest list :=
match list with a :: l => let res := lrest l in append res (append a ". ")
               | nil => ""
end.

(* Fail if the board is invalid, end the proof when it is won *)
Ltac STOP v := match goal with
  |- Invalid_Move => fail 1
| |- Won _ => let v1 := eval compute in (lrest v) in idtac v1; F
| |- _ => idtac
end.

(* Solving tactic *)
Ltac solver v :=
(Rf; STOP ("R" :: v); solver ("R" :: v); fail) || 
(Df; STOP ("D" :: v); solver ("D" :: v); fail) || 
(Lf; STOP ("L" :: v); solver ("L" :: v); fail) || 
(Uf; STOP ("U" :: v); solver ("U" :: v); fail).

Ltac solve := solver constr:(@nil string).

(* Trick the prettyprinter *)

Notation "[T2048]  a " := (games _ _ _ _ _ _ _ a) (at level 10).
Notation "! Won" := (Won _) (at level 10).


(******************************************************************************)
(* In order to win the game we have to provide a list of moves                *)
(* A game is parametrised by a seed that determines which of 2 and 4 appears  *)
(* and where (there is no random number inside Coq ;-) )                      *)
(* You can either give the winning list of moves or try to build it           *)
(*  interactively :                                                           *)
(*       S to start                                                           *)
(*       D to move down                                                       *)
(*       U to move up                                                         *)
(*       R to move right                                                      *)
(*       L to move left                                                       *)
(*       F to end a winning game                                              *)
(******************************************************************************)


(* An example *)
Definition seed := 0. (* The 2 always appears in the first free cell *)

Lemma thm1 : exists ms, g2048 seed ms.
Proof.
S.
R. R. R. R. R. R. R. R. R. R. R. R. R. R. D. R. R. R. R. R. R. R. R. R. R. R. R.
R. R. D. R. R. R. R. R. R. R. R. R. R. R. R. R. R. D. R. R. R. R. R. R. R. R. R.
R. R. R. R. R. D. R. R. R. R. R. R. R. R. R. R. R. R. R. R. D. R. R. R. R. R. R.
R. R. R. R. R. R. R. R. D. R. R. R. R. R. R. R. R. R. R. R. R. R. R. D. R. R. R.
R. R. R. R. R. R. R. R. R. R. R. D. R. R. R. R. R. R. R. R. R. R. R. R. R. R. D.
R. R. R. R. R. R. R. R. R. R. R. R. R. R. D. R. R. R. R. R. R. R. R. R. R. R. R.
R. R. D. R. R. R. R. R. R. R. R. R. R. R. R. R. R. D. R. R. R. R. R. R. R. R. R.
R. R. R. R. R. D. R. R. R. R. R. R. R. R. R. R. R. R. R. R. D. R. R. R. R. R. R.
R. R. R. R. R. R. R. L. D. R. R. R. R. R. R. R. R. R. R. R. R. R. D. R. R. R. R.
R. R. R. R. D. R. R. R. R. R. R. R. R. R. R. R. R. D. R. R. D. R. R. R. R. R. R.
D. R. R. R. R. R. R. D. R. D. R. R. D. R. R. D. R. L. D. R. R. R. R. R. R. R. R.
R. R. R. R. R. D. R. R. R. R. R. R. R. R. D. R. R. R. R. D. R. R. U. R. R. R. R.
R. R. R. D. R. R. R. R. R. R. D. R. R. R. R. R. R. D. R. R. R. R. R. R. D. R. R.
R. R. R. R. D. R. R. R. R. R. R. D. R. R. R. R. R. R. D. D. D. D. D. D. U. R. R.
R. D. R. R. D. R. R. D. R. R. D. R. R. D. R. R. D. R. R. D. D. D. D. D. D. U. R.
D. R. R. D. D. D. D. D. D. D. D. D. D. D. U. R. D. D. D. D. D. D. D. D. D. D. U.
U. R. R. R. R. R. R. R. D. R. R. R. R. R. R. R. R. R. R. R. R. R. R. D. R. R. R.
R. R. R. R. R. R. R. R. R. R. R. D. R. R. R. R. R. R. D. R. R. D. R. R. D. R. R.
D. R. R. D. D. D. D. D. D. U. R. R. R. R. R. R. R. D. R. R. R. R. R. R. D. R. R.
R. R. R. R. D. R. R. D. R. R. D. R. R. D. R. R. D. D. D. D. D. D. U. R. R. R. D.
R. R. D. R. R. D. D. D. D. D. D. D. D. D. D. U. R. D. U. R. R. R. R. R. R. R. D.
R. R. D. R. R. D. R. R. D. D. D. D. D. D. D. D. U. R. R. R. R. R. R. R. D. R. R.
R. R. R. R. D. R. R. R. R. R. L. D. R. R. D. R. R. R. R. D. R. R. R. R. D. R. R.
U. R. R. R. D. R. R. R. R. U. R. D. R. R. R. R. D. R. R. R. R. R. R. R. R. R. R.
R. R. R. D. R. R. R. R. R. R. D. R. R. R. R. D. R. R. R. R. R. R. D. R. R. D. R.
R. D. R. R. D. D. D. D. D. D. D. D. U. R. R. R. R. R. R. R. D. R. R. D. R. R. D.
D. D. D. D. D. D. D. D. D. U. R. R. R. D. U. R. R. R. R. D. R. R. D. R. R. D. D.
D. D. D. D. D. D. U. R. R. R. D. R. R. D. R. L. D. R. R. D. U. R. D. R. R. D. R.
R. D. R. R. D. R. R. D. R. R. D. D. D. D. D. D. U. R. D. D. D. D. D. D. D. D. D.
D. U. U. R. R. R. D. R. R. D. R. R. D. D. D. D. D. D. D. D. D. U. R. D. U. R. U.
D. L. D. R. R. R. R. R. R. R. R. R. R. R. R. R. D. R. R. R. R. R. R. R. R. R. R.
D. R. R. R. R. R. R. R. R. R. R. D. R. R. R. R. R. R. U. R. R. R. R. R. R. L. D.
R. R. R. R. R. R. L. D. R. R. R. R. R. R. R. R. R. R. R. R. R. D. R. R. R. R. D.
R. R. D. R. R. R. R. D. R. R. U. R. R. R. D. R. R. R. R. R. R. R. R. R. R. R. R.
R. D. R. R. D. D. D. D. D. D. D. D. D. U. R. R. R. R. R. R. R. D. R. R. D. R. R.
D. R. R. D. R. R. D. R. R. D. R. R. D. D. D. D. D. D. U. R. R. R. D. D. D. D. D.
D. D. D. D. D. D. D. U. L. D. R. R. R. R. R. R. R. R. R. R. R. R. R. D. U. R. R.
R. R. R. R. R. D. R. R. R. R. R. R. D. R. R. R. R. R. R. D. D. D. D. D. D. D. D.
D. U. R. R. R. D. R. R. D. R. L. D. R. R. D. U. R. D. R. R. D. D. D. D. D. D. D.
D. D. D. U. R. D. U. R. U. D. L. D. R. R. R. R. R. R. R. R. R. R. R. R. R. D. R.
D. R. R. U. R. R. R. R. R. R. L. D. R. R. L. D. R. R. R. R. R. D. R. R. R. R. R.
R. R. R. R. R. U. R. R. R. R. R. R. R. D. R. R. R. R. R. R. R. R. R. R. D. R. R.
D. R. R. R. R. R. R. D. R. R. D. D. D. D. D. D. D. U. R. R. R. R. R. R. R. D. R.
R. D. R. L. D. R. R. R. R. R. R. R. R. R. R. L. L. D. R. R. R. R. R. R. R. R. R.
R. R. R. D. R. R. D. R. L. D. R. L. D. L. R. U. R. R. R. D. R.
F.
Qed.

Lemma thm2 : exists ms, g2048 seed ms.
Proof.
S.
solve.
Qed.

(* 
Lemma thm3 : forall seed, exists ms, g2048 seed ms.
*)