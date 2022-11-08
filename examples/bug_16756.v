(* The exn here can't be printed using a sid *)
Goal True.
Proof.
  unshelve refine (let x := _ : nat in _);[
      abstract exact 0
    | match goal with x := ?v |- _ => exact v end].

Definition foo := 3.
