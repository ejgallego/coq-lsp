type t =
  { mem_stats : bool [@default false]
        (** [mem_stats] Call [Obj.reachable_words] for every sentence. This is
            very slow and not very useful, so disabled by default *)
  ; gc_quick_stats : bool [@default true]
        (** [gc_quick_stats] Show the diff of [Gc.quick_stats] data for each
            sentence *)
  ; eager_diagnostics : bool [@default true]
        (** [eager_diagnostics] Send (full) diagnostics after processing each *)
  ; ok_diagnostics : bool [@default false]  (** Show diagnostic for OK lines *)
  ; goal_after_tactic : bool [@default false]
        (** When showing goals and the cursor is in a tactic, if false, show
            goals before executing the tactic, if true, show goals after *)
  ; show_coq_info_messages : bool [@default false]
        (** Ignore `msg_info` messages in diagnostics *)
  }

let default =
  { mem_stats = false
  ; gc_quick_stats = true
  ; eager_diagnostics = true
  ; ok_diagnostics = false
  ; goal_after_tactic = false
  ; show_coq_info_messages = false
  }

let v = ref default
