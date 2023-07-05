(************************************************************************)
(* Coq Language Server Protocol -- Requests                             *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2019-2023 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

module Sentence : sig
  type t =
    { loc : Lang.Range.t
    ; time : float
    ; mem : float
    }
end

type t =
  { summary : string
  ; timings : Sentence.t list
  }
