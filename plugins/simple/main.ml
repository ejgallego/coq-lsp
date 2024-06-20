open Fleche

let msg_info ~io = Io.(Report.msg ~io ~lvl:Info)

let simple_action ~io ~token:_ ~(doc : Doc.t) =
  msg_info ~io "[example plugin] file checking for %a was completed"
    Lang.LUri.File.pp doc.uri

let main () = Theory.Register.Completed.add simple_action
let () = main ()
