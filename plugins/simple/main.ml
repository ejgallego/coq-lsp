open Fleche

let simple_action ~io ~doc =
  let uri = Lang.LUri.File.to_string_uri doc.Doc.uri in
  let lvl = Io.Level.info in
  let message =
    Format.asprintf "[example plugin] file checking for %s was completed" uri
  in
  Io.Report.message ~io ~lvl ~message

let main () = Theory.Register.add simple_action
let () = main ()
