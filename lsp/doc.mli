(************************************************************************)
(* Coq Language Server Protocol                                         *)
(* Copyright 2019 MINES ParisTech -- LGPL 2.1+                          *)
(* Copyright 2019-2023 Inria -- LGPL 2.1+                               *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

module VersionedTextDocument : sig
  type t =
    { uri : Lang.LUri.File.t
    ; version : int
    }
  [@@deriving yojson]
end
