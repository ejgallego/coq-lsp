(************************************************************************)
(* Coq Language Server Protocol                                         *)
(* Copyright 2019 MINES ParisTech -- LGPL 2.1+                          *)
(* Copyright 2019-2023 Inria -- LGPL 2.1+                               *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

module Point : sig
  type t = Lang.Point.t [@@deriving yojson]
end

module Range : sig
  type t = Lang.Range.t [@@deriving yojson]
end

module LUri : sig
  module File : sig
    type t = Lang.LUri.File.t [@@deriving yojson]
  end
end

module Diagnostic : sig
  type t = Lang.Diagnostic.t [@@deriving yojson]

  module Point : sig
    type t =
      { line : int
      ; character : int
      }
    [@@deriving yojson]
  end

  module Range : sig
    type t =
      { start : Point.t
      ; end_ : Point.t [@key "end"]
      }
    [@@deriving yojson]

    val vnoc : t -> Lang.Range.t
  end
end

module Ast : sig
  module Info : sig
    type t = Lang.Ast.Info.t [@@deriving yojson]
  end
end
