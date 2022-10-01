(* Enable all debug flags *)
let all = false

(* cache *)
let cache = false || all

(* LSP messages: Send and receive *)
let send = true || all
let read = true || all

(* Parsing (this is a bit expensive as it will call the printer *)
let parsing = false || all

(* Backtraces *)
let backtraces = false || all
