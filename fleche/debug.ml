(* Enable all debug flags *)
let all = false

(* cache *)
let cache = false || all

(* LSP messages: Send and receive *)
let send = false || all
let read = false || all

(* finding tokens from a position *)
let find = false || all
let completion = false || all

(* Parsing (this is a bit expensive as it will call the printer *)
let parsing = false || all

(* Backtraces *)
let backtraces = false || all
