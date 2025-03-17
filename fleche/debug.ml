(* This file controls what to trace, we need a better system. As of today, we
   trace using LSP logging facilities, however this is not enough in two cases:

   - logging of the raw protocol itself

   - we don't have a way to filter what we log *)

(* Enable all debug flags *)
let all = false

(* LSP trace flags are now controlled by an option that installs a logger, the
   lsp_init flag should be removed *)
let lsp = false
let lsp_init = false || all || lsp

(* cache *)
let cache = false || all

(* Parsing (this is a bit expensive as it will call the printer *)
let parsing = false || all

(* scanning of prefix-incrementality *)
let scan = false || all

(* Backtraces *)
let backtraces = false || all

(* Unicode conversion *)
let unicode = false || all

(* Sched wakeup *)
let sched_wakeup = false || all

(* Request event queue *)
let request_delay = true || all

(* Competion *)
let completion = false || all

(* Schedule *)
let schedule = true || all
