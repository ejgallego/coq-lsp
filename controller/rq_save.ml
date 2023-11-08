(** Several todos here in terms of usability *)

let request ~doc =
  let open Coq.Protect.E.O in
  let f () =
    (* XXX: What do do with feedback, return to user? *)
    let+ () = Fleche.Doc.save ~doc in
    Ok `Null
  in
  Request.R.of_execution ~name:"save" ~f ()
