(* OK None == EOF *)
val run_tac :
     token:Coq.Limits.Token.t
  -> st:Coq.State.t
  -> ?timeout:float
  -> string
  -> (Coq.State.t option, Loc.t) Coq.Protect.E.t

open Fleche

module ThmDecl : sig
  type t =
    { names : string list
    ; node : Doc.Node.t
    }
end

val get_theorems : doc:Doc.t -> ThmDecl.t list

(** Like [Coq.Interp.interp] but with a timeout *)
val interp :
     ?timeout:float
  -> token:Coq.Limits.Token.t
  -> st:Coq.State.t
  -> Coq.Ast.t
  -> (Coq.State.t, Loc.t) Coq.Protect.E.t

(** From fcc's compiler/output (not yet in public lib) *)
val pp_diags : Format.formatter -> Lang.Diagnostic.t list -> unit

(** [completed_without_error ~doc] returns None, or else if there was some
    problem, the list of erros found, in the form of diagnostics *)
val completed_without_error : doc:Fleche.Doc.t -> Lang.Diagnostic.t list option
