(** Initialize Console Output System *)
val init : Args.Display.t -> Fleche.Io.CallBack.t

(** Report progress on file compilation *)
(* val report : unit -> unit *)

(** Output diagnostics *)
val pp_diags : Format.formatter -> Lang.Diagnostic.t list -> unit
