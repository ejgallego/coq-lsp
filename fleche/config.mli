module Debug : sig
  (** Debug configuration *)

  type t =
    { cache : bool [@default false]  (** Debug info about caching. *)
    ; send : bool [@default false]  (** LSP messages: Send and receive *)
    ; read : bool [@default false]
    ; lsp_init : bool [@default false]
          (** Parsing (this is a bit expensive as it will call the printer *)
    ; parsing : bool [@default false]  (** scanning of prefix-incrementality *)
    ; scan : bool [@default false]  (** Backtraces *)
    ; backtraces : bool [@default false]  (** Unicode conversion *)
    ; unicode : bool [@default false]  (** Sched wakeup *)
    ; sched_wakeup : bool [@default false]  (** Request event queue *)
    ; request_delay : bool [@default true]
    ; mem_stats : bool [@default false] (* TODO: unused? *)
          (** [mem_stats] Call [Obj.reachable_words] for every sentence. This is
              very slow and not very useful, so disabled by default *)
    ; gc_quick_stats : bool [@default true]
          (** [gc_quick_stats] Show the diff of [Gc.quick_stats] data for each
              sentence *)
    }
end

type t =
  { client_version : string [@default "any"]
  ; eager_diagnostics : bool [@default true]
        (** [eager_diagnostics] Send (full) diagnostics after processing each *)
  ; ok_diagnostics : bool [@default false]  (** Show diagnostic for OK lines *)
  ; goal_after_tactic : bool [@default false]
        (** When showing goals and the cursor is in a tactic, if false, show
            goals before executing the tactic, if true, show goals after *)
  ; show_coq_info_messages : bool [@default false]
        (** Show `msg_info` messages in diagnostics *)
  ; show_notices_as_diagnostics : bool [@default false]
        (** Show `msg_notice` messages in diagnostics *)
  ; admit_on_bad_qed : bool [@default true]
        (** [admit_on_bad_qed] There are two possible error recovery strategies
            when a [Qed] fails: one is not to add the constant to the state, the
            other one is admit it. We find the second behavior more useful, but
            YMMV. *)
  ; debug : Debug.t
        [@default
          (* Cannot use Debug.none here :-( *)
          { cache = false
          ; send = false
          ; read = false
          ; lsp_init = false
          ; parsing = false
          ; scan = false
          ; backtraces = false
          ; unicode = false
          ; sched_wakeup = false
          ; request_delay = false
          ; mem_stats = false
          ; gc_quick_stats = false
          }]
  }

(** Current configuration. *)
val v : t ref

(** Enable all debug options. *)
val debug_all : unit -> unit

(** Enable all LSP related debug options. *)
val debug_lsp : unit -> unit
