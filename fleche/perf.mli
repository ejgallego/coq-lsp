(************************************************************************)
(* Coq Language Server Protocol -- Requests                             *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2019-2023 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

module Sentence : sig
  type t =
    { range : Lang.Range.t
    ; time : float
    ; memory : float
    }
end

type t =
  { summary : string
  ; timings : Sentence.t list
  }
