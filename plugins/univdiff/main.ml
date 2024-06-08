open Fleche

let rec dump_univs ~token ~contents fmt (nuniv_prev, nconst_prev)
    (qed_total, qed_yes) (nodes : Doc.Node.t list) =
  match nodes with
  | [] -> Format.fprintf fmt "qed_total: %d / qed_yes: %d" qed_total qed_yes
  | next :: nodes -> (
    let st = next.state in
    let raw = Fleche.Contents.extract_raw ~contents ~range:next.range in
    let qed_total = qed_total + if String.equal "Qed." raw then 1 else 0 in
    match Coq.State.info_universes ~token ~st with
    | Coq.Protect.{ E.r = R.Completed (Ok (nuniv, nconst)); feedback = _ } ->
      let qed_yes =
        qed_yes
        +
        if nuniv_prev <> nuniv || nconst_prev <> nconst then (
          let raw = raw in
          (* maybe trim above ? *)
          Format.fprintf fmt "@[univs for \"%s\":@\n (%4d,%4d) {+%d, +%d}@\n@]"
            raw nuniv nconst (nuniv - nuniv_prev) (nconst - nconst_prev);
          if String.equal "Qed." raw then 1 else 0)
        else 0
      in
      dump_univs ~token ~contents fmt (nuniv, nconst) (qed_total, qed_yes) nodes
    | _ ->
      Format.fprintf fmt "Error!! Terminating!! X_X O_O@\n%!";
      ())

let dump_univs ~token ~out_file (doc : Doc.t) =
  let out = Stdlib.open_out out_file in
  let fmt = Format.formatter_of_out_channel out in
  (match Coq.State.info_universes ~token ~st:doc.root with
  | Coq.Protect.{ E.r = R.Completed (Ok root); feedback = _ } ->
    dump_univs ~token ~contents:doc.contents fmt root (0, 0) doc.nodes
  | _ -> ());
  Format.pp_print_flush fmt ();
  Stdlib.close_out out

let dump_univdiff ~io ~token ~(doc : Doc.t) =
  let uri = doc.uri in
  let uri_str = Lang.LUri.File.to_string_uri uri in
  let out_file = Lang.LUri.File.to_string_file uri ^ ".unidiff" in
  let lvl = Io.Level.info in
  let ndiags = Doc.diags doc |> List.length in
  let message =
    Format.asprintf "[univdiff plugin] %d diags present for file..." ndiags
  in
  Io.Report.message ~io ~lvl ~message;
  let message =
    Format.asprintf "[univdiff plugin] dumping universe diff for %s ..." uri_str
  in
  Io.Report.message ~io ~lvl ~message;
  let () = dump_univs ~token ~out_file doc in
  let message =
    Format.asprintf
      "[univdiff plugin] dumping universe diff for %s was completed!" uri_str
  in
  Io.Report.message ~io ~lvl ~message;
  ()

let main () = Theory.Register.Completed.add dump_univdiff
let () = main ()
