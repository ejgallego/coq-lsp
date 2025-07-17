(************************************************************************)
(* Coq Language Server Protocol                                         *)
(* Copyright 2019 MINES ParisTech -- LGPL 2.1+                          *)
(* Copyright 2019-2023 Inria -- LGPL 2.1+                               *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

module Point : sig
  module Mode : sig
    (** Internally, Flèche always works with a point type which includes
        {i both} line/column and offset information. However, this is beyond the
        LSP standard, so clients can configure the input / output behavior here *)
    type t =
      | LineColumn
          (** Points are standard LSP objects with [line] [character] field;
              this is the default *)
      | Offset  (** Points are objects with only the [offset] *)
      | Full
          (** Points include / require [line], [character], and [offset] field *)

    (** Set the mode for serialization. *)
    val set : t -> unit
  end

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
  module Mode : sig
    (** Flèche diagnostics store the message as a Pp.t box format, but usually
        LSP standard mandates the [message] field to be a string, thus we allow
        clients to select the mode. *)
    type t =
      | String
      | Pp

    val set : t -> unit
  end

  type t = Lang.Diagnostic.t [@@deriving yojson]
end

module Ast : sig
  module Info : sig
    type t = Lang.Ast.Info.t [@@deriving yojson]
  end
end
