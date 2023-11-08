(** Several todos here in terms of usability *)

let request ~doc =
  let open Coq.Protect.E.O in
  let f () =
    let+ () = Fleche.Doc.save ~doc in
    Ok `Null
  in
  Request.R.of_execution ~name:"save" ~f ()
