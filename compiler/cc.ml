(* Compiler context *)
type t =
  { root_state : Coq.State.t
  ; workspaces : (string * Coq.Workspace.t) list
  ; io : Fleche.Io.CallBack.t
  }
