(******************************************************************************)
(*                  This file is part of Waterproof-lib.                      *)
(*                                                                            *)
(*   Waterproof-lib is free software: you can redistribute it and/or modify   *)
(*    it under the terms of the GNU General Public License as published by    *)
(*     the Free Software Foundation, either version 3 of the License, or      *)
(*                    (at your option) any later version.                     *)
(*                                                                            *)
(*     Waterproof-lib is distributed in the hope that it will be useful,      *)
(*      but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*       MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the         *)
(*               GNU General Public License for more details.                 *)
(*                                                                            *)
(*     You should have received a copy of the GNU General Public License      *)
(*   along with Waterproof-lib. If not, see <https://www.gnu.org/licenses/>.  *)
(*                                                                            *)
(******************************************************************************)

Require Import Ltac2.Ltac2.
Require Import Ltac2.Message.
Local Ltac2 concat_list (ls : message list) : message :=
  List.fold_right concat ls (of_string "").

(** Tries to make the assertion [True] with label [label].
  Throws an error if this fails, i.e. if the label is already used
  for another one of the hypotheses.
  
  This check was separated out from the 'assert'-tactics below because the 
  '[label] is already used error' would otherwise be caught in
  the code meant to catch [AutomationFailure] errors. *)

Local Ltac2 try_out_label (label : ident) :=
  match Control.case (fun () => 
    assert True as $label by exact I)
  with
  | Err exn => Control.zero exn
  | Val _ => clear $label
  end.

(* For making tests independent of WaterProof *)
Ltac2 warn : message -> unit := fun _ => ().
Ltac2 throw : message -> unit := fun _ => (). 
Ltac2 waterprove (_depth: int) (_shield: bool) (_db_type: 'a) := ().
Ltac2 rwaterprove (_depth: int) (_shield: bool) (_db_type: 'a) (_ : constr) := ().
Ltac2 suggest_how_to_use (_x : constr) (_label : ident option) := ().
Ltac2 Type exn ::= [ FailedToProve(constr) ].
Ltac2 correct_type_by_wrapping (t: constr): constr := t.
Ltac2 wrapper_core_by_tactic (_by_tactic : constr -> unit) (_xtr_lemma : constr) := ().
Ltac2 panic_if_goal_wrapped () := ().
Ltac2 since_framework (_by_tactic : constr -> unit) (_claimed_cause : constr) := ().

(** Attempts to assert that [claim] holds, if succesful [claim] is added to the local
  hypotheses. If [label] is specified [claim] is given [label] as its identifier, otherwise an
  identifier starting with '_H' is generated.
  
  Additionally, if argument [postpone] is [true], actually proving the claim is postponed.
  The claim is asserted and the proof is shelved using an evar.
  *)
Local Ltac2 wp_assert (claim : constr) (label : ident option) (postpone : bool):=
  let err_msg (g : constr) := concat_list
    [of_string "Could not verify that "; of_constr g; of_string "."] in
  let id := 
    match label with 
    | None => Fresh.in_goal @_H
    | Some label => try_out_label label; label
    end
  in
  let claim := claim in
  if postpone
    then
      (* Assert claim and proof using shelved evar *)
      (* (using 'admit' would have shown a confusing warning message) *)
      assert $claim as $id;
      Control.focus 1 1 (fun () =>
        let evar_id := Fresh.in_goal @_Hpostpone in
        ltac1:(id claim |- evar (id : claim)) (Ltac1.of_ident evar_id) (Ltac1.of_constr claim); 
        let evar := Control.hyp evar_id in 
        exact $evar
        );
      warn (concat_list [of_string "Please come back later to provide an actual proof of ";
        of_constr claim; of_string "."])
      
    else
      (* Assert claim and attempt to prove automatically *)
      match Control.case (fun () =>
        assert $claim as $id by 
          (waterprove 5 true 99))
      with
      | Val _ => ()
      | Err (FailedToProve g) => throw (err_msg g)
      | Err exn => Control.zero exn
      end;
  (* Print suggestion on how to use new statement. *)
  suggest_how_to_use claim label.

(** Attempts to assert that [claim] holds, if succesful [claim] is added to the local
  hypotheses. If [label] is specified [claim] is given [label] as its identifier, otherwise an
  identifier starting with '_H' is generated.
  [xtr_lemma] has to be used in the proof that [claim] holds.
  *)
Local Ltac2 core_wp_assert_by (claim : constr) (label : ident option) (xtr_lemma : constr) :=
  let err_msg (g : constr) := concat_list
    [of_string "Could not verify that "; of_constr g; of_string "."] in
  let id := 
    match label with 
    | None => Fresh.in_goal @_H
    | Some label => try_out_label label; label
    end
  in
  let claim := correct_type_by_wrapping claim in
  match Control.case (fun () =>
    assert $claim as $id by 
      (rwaterprove 5 true 19 xtr_lemma))
  with
  | Val _ => ()
  | Err (FailedToProve g) => throw (err_msg g)
  | Err exn => Control.zero exn (* includes FailedToUse error *)
  end.

(** Adaptation of [core_wp_assert_by] that turns the [FailedToUse] errors 
  which might be thrown into user readable errors. *)
Local Ltac2 wp_assert_by (claim : constr) (label : ident option) (xtr_lemma : constr) :=
  wrapper_core_by_tactic (core_wp_assert_by claim label) xtr_lemma;
  (* Print suggestion on how to use new statement. *)
  suggest_how_to_use claim label.

(** Adaptation of [core_wp_assert_by] that allows user to use mathematical statements themselves
  instead of references to them as extra information for the automation system.
  Uses the code in [Since.v]. *)
Local Ltac2 wp_assert_since (claim : constr) (label : ident option) (xtr_claim : constr) :=
  since_framework (core_wp_assert_by claim label) xtr_claim;
  (* Print suggestion on how to use new statement. *)
  suggest_how_to_use claim label.


(**
  Attempts to assert a claim and proves it automatically using a specified lemma, 
  this lemma has to be used.

  Arguments:
    - [xtr_lemma: constr], reference to a lemma used to prove the claim (via [rwaterprove]).
    - [label: ident option], optional name for the claim. 
        If the proof succeeds, it will become a hypothesis (bearing [label] as name).
    - [claim: constr], the actual content of the claim to prove.

    Raises exception:
    - (fatal) if [rwaterprove] fails to prove the claim using the specified lemma.
    - [[label] is already used], if there is already another hypothesis with identifier [label].
*)
Ltac2 Notation "By" xtr_lemma(constr) "it" "holds" "that" claim(constr) label(opt(seq("(", ident, ")"))) :=
  panic_if_goal_wrapped ();
  wp_assert_by claim label xtr_lemma.

Ltac2 Notation "Since" xtr_claim(constr) "it" "holds" "that" claim(constr) label(opt(seq("(", ident, ")"))) :=
  panic_if_goal_wrapped ();
  wp_assert_since claim label xtr_claim.
    
  
(** * It holds that ... (...)
  Attempts to assert a claim and proves it automatically.
  Removes [StateHyp.Wrapper] wrapper from the goal (proving claim by automation not necessary).

  Arguments:
    - [label: ident option], optional name for the claim. 
        If the proof succeeds, it will become a hypothesis (bearing [label] as name).
    - [claim: constr], the actual content of the claim to prove.

    Raises exception:
    - (fatal) if [rwaterprove] fails to prove the claim using the specified lemma.
    - [[label] is already used], if there is already another hypothesis with identifier [label].
    - (fatal) If goal is wrapped in [StateHyp.Wrapper] and the wrong statement is specified.
*)
Inductive Wrapper (A : Type) (h : A) (G : Type) : Type :=
    | wrap : G -> Wrapper A h G.
Ltac2 check_constr_equal (_a: constr) (_b: constr) := false.

Local Ltac2 wp_assert_with_unwrap (claim : constr) (label : ident option) :=
  (* Try out label first. 
    Code results in wrong error if done inside repeated match.. *)
  match label with | None => () | Some label => try_out_label label end;
  
  match! goal with
  | [h : ?s |- Wrapper ?s ?h_spec _] => 
    let h_constr := Control.hyp h in
    (* sanity check "h = h_spec" *)
    if check_constr_equal h_constr h_spec
      then ()
      else fail;
    let w := match label with
      | None => Fresh.fresh (Fresh.Free.of_goal ()) @_H
      | Some label => label
      end in
    if check_constr_equal s claim
      then
        match Control.case (fun () => assert $claim as $w by exact $h_constr) with
        | Val _ =>  (* If claims are definitionally equal, go with the
                  version that is supplied as argument to "It holds that ..." *)
          apply (wrap $s);
          Std.clear [h]
        | Err exn => print (of_string "Exception occurred"); print (of_exn exn)
        end
      else throw (of_string "Wrong statement specified.")
    (* rename ident generated in specialize with user-specified label*)
    (* match label with
    | None => ()
    | Some label => Std.rename [(w, label)]
    end *)
  | [|- _] => 
    panic_if_goal_wrapped ();
    wp_assert claim label false
  end.

Ltac2 Notation "It" "holds" "that" claim(constr) label(opt(seq("(", ident, ")")))  :=
  wp_assert_with_unwrap claim label.


(** * By magic it holds that ... (...)
  Asserts a claim and proves it using a shelved evar.

  Arguments:
    - [label: ident option], optional name for the claim. 
    - [claim: constr], the actual content of the claim to prove.

    Raises exception:
    - [[label] is already used], if there is already another hypothesis with identifier [label].

    Raises warning:
    - [Please come back later to provide an actual proof of [claim].], always.
*)

Ltac2 Notation "By" "magic" "it" "holds" "that" claim(constr) label(opt(seq("(", ident, ")"))) := 
  panic_if_goal_wrapped ();
  wp_assert claim label true.