module State = Internal.Make (struct
  type coq = Vernacstate.Parser.t
end)

module Proof_mode = Internal.Make (struct
  type coq = Pvernac.proof_mode
end)

module Parsable = struct
  type t = Pcoq.Parsable.t

  let make = Pcoq.Parsable.make
end

let parse st mode ps =
  let st = State.Internal.to_coq st in
  let mode = Option.map Proof_mode.Internal.to_coq mode in
  Vernacstate.Parser.parse st Pvernac.(main_entry mode) ps
  |> Option.map Ast.Internal.of_coq

(* Error recovery heuristic *)

(* Read the input stream until a dot or a "end of proof" token is encountered *)
let parse_to_terminator : unit Pcoq.Entry.t =
  (* type 'a parser_fun = { parser_fun : te LStream.t -> 'a } *)
  let rec dot st =
    match Gramlib.LStream.next st with
    | Tok.KEYWORD ("." | "..." | "Qed" | "Defined" | "Admitted") | Tok.BULLET _
      -> ()
    | Tok.EOI -> ()
    | _ -> dot st
  in
  Pcoq.Entry.of_parser "Coqtoplevel.dot" { parser_fun = dot }

(* If an error occurred while parsing, we try to read the input until a dot
   token is encountered. We assume that when a lexer error occurs, at least one
   char was eaten *)

let rec discard_to_dot ps =
  try Pcoq.Entry.parse parse_to_terminator ps with
  | CLexer.Error.E _ -> discard_to_dot ps
  | e when CErrors.noncritical e -> ()
