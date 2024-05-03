(************************************************************************)
(* Coq Language Server Protocol -- Requests                             *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2019-2023 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

module Info : sig
  type t =
    { time : float  (** Original Execution Time (when not cached) *)
    ; memory : float
          (** Difference in words allocated in the heap using `Gc.quick_stat` *)
    ; cache_hit : bool  (** was the sentence cached? *)
    ; time_hash : float  (** Memo timing overhead *)
    }
end

module Sentence : sig
  type t =
    { range : Lang.Range.t
    ; info : Info.t
    }
end

type t =
  { summary : string
  ; timings : Sentence.t list
  }
