(**
   Plugin to convert a literate Coq LaTeX document into a simple LaTeX one
   that can be directly compiled.
*)
open Fleche

let convert_to_latex ~io ~token ~(doc: Doc.t) : unit =
  let _io = io in
  let _token = token in
  let _doc = doc in
  ()

let () = Theory.Register.Completed.add convert_to_latex
