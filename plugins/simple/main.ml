let simple_action ~io:_ ~doc =
  let uri = Lang.LUri.File.to_string_uri doc.Fleche.Doc.uri in
  Format.eprintf "[example plugin] file checking for %s was completed@\n%!" uri

let main () = Fleche.Theory.Register.add simple_action
let () = main ()
