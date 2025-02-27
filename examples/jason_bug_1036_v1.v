(* test-kind: error in exec *)
(* for testing with fcc too *)

(* -*- mode: coq; coq-prog-args: ("-emacs" "-w" "-deprecated-native-compiler-option,-native-compiler-disabled" "-native-compiler" "ondemand" "-R" "." "IsomorphismChecker" "-top" "IsomorphismChecker.DemoChecker") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 82 lines to 100 lines, then from 108 lines to 450 lines, then from 455 lines to 155 lines, then from 162 lines to 175 lines, then from 180 lines to 161 lines, then from 168 lines to 285 lines, then from 288 lines to 61 lines, then from 56 lines to 47 lines, then from 54 lines to 1377 lines, then from 1380 lines to 149 lines, then from 156 lines to 209 lines, then from 214 lines to 181 lines, then from 188 lines to 368 lines, then from 372 lines to 219 lines, then from 224 lines to 220 lines *)
(* coqc version 9.1+alpha compiled with OCaml 4.14.2
   coqtop version 9.1+alpha
   Expected coqc runtime on this file: 0.127 sec *)

Require Stdlib.derive.Derive.
Require Stdlib.Arith.Arith.
Require Ltac2.Ltac2.

Module Export AdmitTactic.
Module Import LocalFalse.
End LocalFalse.
End AdmitTactic.

Module Export IsomorphismChecker_DOT_Original_WRAPPED.
Module Export Original.
Import Stdlib.Lists.List.

Inductive binop : Set := Plus | Times.

Inductive exp : Set :=
 Const : nat -> exp
| Binop : binop -> exp -> exp -> exp.
Fixpoint expDenote (e: exp) : nat.
Admitted.

Inductive instr: Set :=
| iConst : nat -> instr
| iBinop : binop -> instr.

Definition prog := list instr.

Definition stack := list nat.
Fixpoint progDenote (p : prog) (s: stack) : option stack.
Admitted.
Fixpoint compile (e : exp): prog.
Admitted.

Definition compile_one_instr_statement:= forall e p s, progDenote (compile e ++ p) s = progDenote p (expDenote e :: s).

End Original.

End IsomorphismChecker_DOT_Original_WRAPPED.
Module Export IsomorphismChecker_DOT_Original.
Module Export IsomorphismChecker.
Module Original.
Include IsomorphismChecker_DOT_Original_WRAPPED.Original.
End Original.

End IsomorphismChecker.

End IsomorphismChecker_DOT_Original.
Module IsomorphismChecker_DOT_IsomorphismDefinitions_WRAPPED.
Module Export IsomorphismDefinitions.
#[export]
Set Universe Polymorphism.
Inductive eq@{s|u|} {α:Type@{s|u}} (a:α) : α -> SProp
  := eq_refl : eq a a.

#[local] Notation "x = y" := (eq x y) : type_scope.
#[export]
Set Implicit Arguments.
Cumulative Record Iso@{s s'|u u'|} (A : Type@{s|u}) (B : Type@{s'|u'}) := {
    to :> A -> B;
    from : B -> A;
    to_from : forall x, to (from x) = x;
    from_to : forall x, from (to x) = x;
}.

Definition rel_iso@{s s'|u u'|} {A B} (i : Iso@{s s'|u u'} A B) : A -> B -> _ := fun x y => i.(to) x = y.

Existing Class Iso.

End IsomorphismDefinitions.

End IsomorphismChecker_DOT_IsomorphismDefinitions_WRAPPED.
Module Export IsomorphismChecker_DOT_IsomorphismDefinitions.
Module Export IsomorphismChecker.
Module IsomorphismDefinitions.
Include IsomorphismChecker_DOT_IsomorphismDefinitions_WRAPPED.IsomorphismDefinitions.
End IsomorphismDefinitions.

End IsomorphismChecker.

End IsomorphismChecker_DOT_IsomorphismDefinitions.
Module Export IsomorphismChecker_DOT_Automation_WRAPPED.
Module Export Automation.
Import IsomorphismChecker.IsomorphismDefinitions.
Inductive MatchPair {A B} := match_pair (a : A) (b : B).
Variant print_as_iso_statement@{s s'|u u'|} {A : Type@{s|u}} {B : Type@{s'|u'}} (a : A) (b : B) : SProp := .
Import Ltac2.Ltac2.
Module Export Constr.
Import Ltac2.Constr.
Ltac2 is_sort_or_evar(c: constr) :=
  match Unsafe.kind c with
  | Unsafe.Sort _ => true
  | Unsafe.Evar _ _ => true
  | _ => false
  end.

Ltac2 in_context_prod n t f :=
  let c := Constr.in_context n t f in
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Lambda n b => Constr.Unsafe.make (Constr.Unsafe.Prod n b)
  | _ => Control.throw (Invalid_argument (Some (Message.of_constr c)))
  end.
End Constr.
Module Export Fresh.
Import Ltac2.Fresh.
Ltac2 fresh' (b : Free.t) (id : ident) := let id := fresh b id in (id, Fresh.Free.union b (Free.of_ids [id])).
End Fresh.

Import Ltac2.Printf.

Ltac2 fail fmt := Message.Format.kfprintf (fun msg => Control.zero (Tactic_failure (Some msg))) fmt.
Ltac2 Notation "fail" fmt(format) := fail fmt.

Import Ltac2.Bool.BoolNotations.

Ltac2 rec iso_statement f1 f2 :=
  let f1 := (eval cbv beta in $f1) in
  let f2 := (eval cbv beta in $f2) in
  let t1 := Constr.type f1 in
  let t2 := Constr.type f2 in
  if (Constr.is_sort t1 || Constr.is_sort t2) && Constr.is_sort_or_evar t1 && Constr.is_sort_or_evar t2
  then '(Iso $f1 $f2)
  else
    let handle_forall a1 a2 :=
      let b := Fresh.Free.of_goal () in
      let (x1, b) := Fresh.fresh' b @x1 in
      let (x2, b) := Fresh.fresh' b @x2 in
      let (hx, _b) := Fresh.fresh' b @hx in
      Constr.in_context_prod x1 a1 (fun () => Control.refine (fun () =>
        Constr.in_context_prod x2 a2 (fun () => Control.refine (fun () =>
          Constr.in_context_prod hx (iso_statement (Control.hyp x1) (Control.hyp x2)) (fun () => Control.refine (fun () =>
            let x1 := Control.hyp x1 in let x2 := Control.hyp x2 in iso_statement '($f1 $x1) '($f2 $x2)))))))
    in
    lazy_match! '(match_pair $t1 $t2) with
    | match_pair (forall x1 : ?a1, _) (forall x2 : ?a2, _) => handle_forall a1 a2
    | match_pair (forall x1 : ?a1, _) _ => handle_forall a1 '_
    | match_pair _ (forall x2 : ?a2, _) => handle_forall '_ a2
    | _ =>
      match Control.case (fun () => constr:(rel_iso _ $f1 $f2)) with
      | Val (c, _) => c
      | Err err =>
        let (i1, i1_args) := Constr.decompose_app t1 in
        let (i2, i2_args) := Constr.decompose_app t2 in
        let extra :=
          let i1_ind := Constr.is_ind i1 in
          let i2_ind := Constr.is_ind i2 in
          let i1_evar := Constr.is_evar i1 in
          let i2_evar := Constr.is_evar i2 in
          let i1_args0 := Int.equal (Array.length i1_args) 0 in
          let i2_args0 := Int.equal (Array.length i2_args) 0 in
          let args_eq := Int.equal (Array.length i1_args) (Array.length i2_args) in
          if (i1_ind && i2_ind && args_eq)
            || (i1_ind && i2_evar && i2_args0)
            || (i2_ind && i1_evar && i1_args0)
          then fprintf "Consider adding %t: " '(print_as_iso_statement $i1 $i2)
          else fprintf "" in
        fail "%aCould not find an isomorphism of type %t (for %t): %a" (fun _ m => m) extra '(Iso $t1 $t2) '(rel_iso _ $f1 $f2) (fun () => Message.of_exn) err
      end
    end.

Ltac2 import_of (f : constr) :=
  match Control.case (fun () =>
    let t := '_ in
    let f2 := Fresh.in_goal @f2 in
    let _ := Constr.in_context f2 t (fun () =>
      Control.refine (fun () => iso_statement f (Control.hyp f2))) in
    t)
  with
  | Val (t, _) => t
  | Err err =>
    let msg := match err with
      | Tactic_failure (Some msg) => msg
      | _ => Message.of_exn err
    end in
    let msg := fprintf "While importing %t: %a" f (fun () a => a) msg in

    fail "%a" (fun () m => m) msg
  end.

Notation import_of f := (match f return _ with _ => ltac2:(Control.refine (fun () => import_of (Constr.pretype f))) end) (only parsing).

End Automation.

End IsomorphismChecker_DOT_Automation_WRAPPED.
