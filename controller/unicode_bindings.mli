(** * Unicode bindings for completion table *)

(** Small subset of the supported bindings for unicode characters in a table.
    Useful for debugging. *)
val small : (string * string) list

(** Two set of binding, regular unicode symbols *)
val normal : (string * string) list

(** All the supported bindings for unicode characters in a table. *)
val extended : (string * string) list

(** Return the list selected in config *)
val from_config : unit -> (string * string) list
