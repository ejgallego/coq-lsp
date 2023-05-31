module Unicode_completion = struct
  type t =
    | Off
    | Internal_small
    | Normal
    | Extended
end

type t =
  { mem_stats : bool [@default false]
        (** [mem_stats] Call [Obj.reachable_words] for every sentence. This is
            very slow and not very useful, so disabled by default *)
  ; gc_quick_stats : bool [@default true]
        (** [gc_quick_stats] Show the diff of [Gc.quick_stats] data for each
            sentence *)
  ; client_version : string [@default "any"]
  ; eager_diagnostics : bool [@default true]
        (** [eager_diagnostics] Send (full) diagnostics after processing each *)
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
  ; debug : bool [@default false]
        (** Enable debug on Coq side, including backtraces *)
  ; unicode_completion : Unicode_completion.t
        [@default Unicode_completion.Normal]
  ; max_errors : int [@default 150]
  ; pp_type : int [@default 0]
        (** Pretty-printing type in Info Panel Request, 0 = string; 1 = Pp.t; 2
            = Coq Layout Engine *)
  ; show_stats_on_hover : bool [@default false]
  ; verbosity : int [@default 2]
  ; pp_json : bool [@default false]
  }

let default =
  { mem_stats = false
  ; gc_quick_stats = true
  ; client_version = "any"
  ; eager_diagnostics = true
  ; goal_after_tactic = false
  ; show_coq_info_messages = false
  ; show_notices_as_diagnostics = false
  ; admit_on_bad_qed = true
  ; debug = false
  ; unicode_completion = Normal
  ; max_errors = 150
  ; pp_type = 0
  ; show_stats_on_hover = false
  ; verbosity = 2
  ; pp_json = false
  }

let v = ref default
