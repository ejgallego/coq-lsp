(* Compiler context *)
type t =
  { root_state : Coq.State.t
  ; workspaces : (string * (Coq.Workspace.t, string) Result.t) list
  ; default : Coq.Workspace.t
  ; io : Fleche.Io.CallBack.t
  }
