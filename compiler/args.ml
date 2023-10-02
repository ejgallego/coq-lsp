module Display = struct
  type t =
    | Verbose
    | Normal
    | Quiet
end

type t =
  { cmdline : Coq.Workspace.CmdLine.t
  ; roots : string list  (** workspace root(s) *)
  ; files : string list  (** files to compile *)
  ; debug : bool  (** run in debug mode *)
  ; display : Display.t  (** display level *)
  ; plugins : string list  (** Flèche plugins to load *)
  }
