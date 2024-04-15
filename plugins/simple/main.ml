open Fleche

let simple_action ~io ~token:_ ~doc =
  let uri = Lang.LUri.File.to_string_uri doc.Doc.uri in
  let lvl = Io.Level.info in
  let message =
    Format.asprintf "[example plugin] file checking for %s was completed" uri
  in
  Io.Report.message ~io ~lvl ~message

let main () = Theory.Register.Completed.add simple_action
let () = main ()
