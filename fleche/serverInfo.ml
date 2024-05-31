(************************************************************************)
(* Coq Language Server Protocol                                         *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2019-202r Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

module Version = struct
  type t =
    { coq : string
    ; ocaml : string
    ; coq_lsp : string
    }
end

module Status = struct
  type t =
    | Stopped
    | Idle of string (* memory use *)
    | Running of string (* modname *)
end
