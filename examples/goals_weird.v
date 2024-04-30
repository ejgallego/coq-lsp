(* Example from Zulip / vsCoq tracker *)
Require Coq.Logic.StrictProp.

Import StrictProp.

Definition gunk {FinalOutputType : Type} : False.
Proof.
  evar (exfalsoS'_type : forall (n : nat), Type).
  evar (exfalsoS' : forall (n : nat), exfalsoS'_type n).
  Unshelve.
  
  Focus 2.
    refine (
        fun (nRemainingArgs : nat) =>
          match nRemainingArgs with
          | 0 => False -> FinalOutputType
          | S n' => _
          end
    ).
  Unfocus.

  Focus 3.
    refine (
        fun (nRemainingArgs : nat) =>
          (_ : (exfalsoS'_type nRemainingArgs))
    ).
    refine (
        match
            nRemainingArgs
            as nRemainingArgs_copy
            return exfalsoS'_type nRemainingArgs_copy
        with
        | 0 => _
        | S nRemainingArgs_pred =>
              fun [ThisArgType : Type] (a : ThisArgType) => _
        end
    ).

(* Check to this point to verify goal printing works ok *)
Definition foo := 3.
