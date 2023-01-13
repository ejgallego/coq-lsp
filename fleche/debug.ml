(* Enable all debug flags *)
let all = false

(* Enable LSP debug flags *)
let lsp = false

(* cache *)
let cache = false || all

(* LSP messages: Send and receive *)
let send = false || all || lsp
let read = false || all || lsp

(* Parsing (this is a bit expensive as it will call the printer *)
let parsing = false || all

(* scanning of prefix-incrementality *)
let scan = false || all

(* Backtraces *)
let backtraces = false || all

(* Sched wakeup *)
let sched_wakeup = false || all

(* Request event queue *)
let request_delay = true || all
