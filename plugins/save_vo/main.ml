open Fleche

(* Improve errors *)
let save_vo_file ~io:_ ~doc =
  match Doc.save ~doc with
  | { r = Completed (Ok ()); feedback = _ } -> ()
  | { r = Completed (Error _); feedback = _ } -> ()
  | { r = Interrupted; feedback = _ } -> ()

let main () = Theory.Register.add save_vo_file
let () = main ()
