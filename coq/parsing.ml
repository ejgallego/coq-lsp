let parse ~st ps =
  let mode = State.mode ~st in
  let st = State.parsing ~st in
  (* Coq is missing this, so we add it here. Note that this MUST run inside
     coq_protect *)
  Control.check_for_interrupt ();
  Vernacstate.Parser.parse st Pvernac.(main_entry mode) ps
  |> Option.map Ast.of_coq

let parse ~st ps = Protect.eval ~f:(parse ~st) ps
