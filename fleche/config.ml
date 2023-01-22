module Debug = struct
  type t =
    { cache : bool
    ; send : bool
    ; read : bool
    ; lsp_init : bool
    ; parsing : bool
    ; scan : bool
    ; backtraces : bool
    ; unicode : bool
    ; sched_wakeup : bool
    ; request_delay : bool
    ; mem_stats : bool
    ; gc_quick_stats : bool
    }

  let all =
    { cache = true
    ; send = true
    ; read = true
    ; lsp_init = true
    ; parsing = true
    ; scan = true
    ; backtraces = true
    ; unicode = true
    ; sched_wakeup = true
    ; request_delay = true
    ; mem_stats = true
    ; gc_quick_stats = true
    }

  let none =
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
    }

  let lsp =
    { cache = false
    ; send = true
    ; read = true
    ; lsp_init = true
    ; parsing = false
    ; scan = false
    ; backtraces = false
    ; unicode = false
    ; sched_wakeup = false
    ; request_delay = false
    ; mem_stats = false
    ; gc_quick_stats = true
    }
end

type t =
  { client_version : string
  ; eager_diagnostics : bool
  ; ok_diagnostics : bool
  ; goal_after_tactic : bool
  ; show_coq_info_messages : bool
  ; show_notices_as_diagnostics : bool
  ; admit_on_bad_qed : bool
  ; debug : Debug.t
  }

let default =
  { client_version = "any"
  ; eager_diagnostics = true
  ; ok_diagnostics = false
  ; goal_after_tactic = false
  ; show_coq_info_messages = false
  ; show_notices_as_diagnostics = false
  ; admit_on_bad_qed = true
  ; debug = Debug.none
  }

let v = ref default
let debug_all () = v := { !v with debug = Debug.all }
let debug_lsp () = v := { !v with debug = Debug.lsp }
