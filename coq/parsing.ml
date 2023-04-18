module Parsable = struct
  include Pcoq.Parsable
  let make = make ?fix_loc:None
end

let parse ~st ps =
  let mode = State.mode ~st in
  let st = State.parsing ~st in
  (* Coq is missing this, so we add it here. Note that this MUST run inside
     coq_protect *)
  Control.check_for_interrupt ();
  Vernacstate.Parser.parse st Pvernac.(main_entry mode) ps
  |> Option.map Ast.of_coq

let parse ~st ps = Protect.eval ~f:(parse ~st) ps

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
