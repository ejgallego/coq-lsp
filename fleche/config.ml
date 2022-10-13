(** [mem_stats] Call [Obj.reachable_words] for every sentence. This is very slow
    and not very useful, so disabled by default *)
let mem_stats = false

(** [gc_quick_stats] Show the diff of [Gc.quick_stats] data for each sentence *)
let gc_quick_stats = true

(** [eager_diagnostics] Send (full) diagnostics after processing each *)
let eager_diagnostics = true

(** Show diagnostic for OK lines *)
let ok_diag = false
