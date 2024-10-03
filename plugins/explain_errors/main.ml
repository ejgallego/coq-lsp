(* Example plugin to print errors with goals *)
(* c.f. https://github.com/coq/coq/issues/19601 *)
open Fleche

let msg_info ~io = Io.(Report.msg ~io ~lvl:Info)

let pp_goals ~token ~st =
  match Coq.State.lemmas ~st with
  | None -> Pp.str "no goals"
  | Some proof -> (
    match Coq.Print.pr_goals ~token ~proof with
    | { Coq.Protect.E.r = Completed (Ok goals); _ } -> goals
    | { Coq.Protect.E.r =
          Completed (Error (User { msg; _ } | Anomaly { msg; _ }))
      ; _
      } -> Pp.(str "error when printing goals: " ++ msg)
    | { Coq.Protect.E.r = Interrupted; _ } ->
      Pp.str "goal printing was interrupted")

module Error_info = struct
  type t =
    { error : Pp.t
    ; command : string
    ; goals : Pp.t
    }

  let print ~io { error; command; goals } =
    msg_info ~io
      "[explain errors plugin]@\n\
       Error:@\n\
      \ @[%a@]@\n\
       @\n\
       when trying to apply@\n\
       @\n\
      \ @[%s@]@\n\
       for goals:@\n\
      \ @[%a@]" Pp.pp_with error command Pp.pp_with goals
end

let extract_errors ~token ~root ~contents (node : Doc.Node.t) =
  let errors = List.filter Lang.Diagnostic.is_error node.diags in
  let st = Option.cata Doc.Node.state root node.prev in
  let command = Contents.extract_raw ~contents ~range:node.range in
  let goals = pp_goals ~token ~st in
  List.map
    (fun { Lang.Diagnostic.message; _ } ->
      { Error_info.error = message; command; goals })
    errors

let explain_error ~io ~token ~(doc : Doc.t) =
  let root = doc.root in
  let contents = doc.contents in
  let errors =
    List.(map (extract_errors ~token ~root ~contents) doc.nodes |> concat)
  in
  msg_info ~io "[explain errors plugin] we got %d errors" (List.length errors);
  List.iter (Error_info.print ~io) errors

let main () = Theory.Register.Completed.add explain_error
let () = main ()
