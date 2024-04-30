open Fleche

(* Improve errors *)
let save_vo_file ~io:_ ~token ~doc =
  match Doc.save ~token ~doc with
  | { r = Completed (Ok ()); feedback = _ } -> ()
  | { r = Completed (Error _); feedback = _ } -> ()
  | { r = Interrupted; feedback = _ } -> ()

let main () = Theory.Register.Completed.add save_vo_file
let () = main ()
