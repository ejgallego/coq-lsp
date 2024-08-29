(************************************************************************)
(* Flèche => RL agent: petanque                                         *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2019-2024 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias & coq-lsp contributors           *)
(************************************************************************)

open Petanque_json

(** [set_workspace { debug; root }] sets the current workspace to the directory
    specified in [root] *)
module SetWorkspace = struct
  let method_ = "petanque/setWorkspace"

  module Params = struct
    type t =
      { debug : bool
      ; root : Lsp.JLang.LUri.File.t
      }
    [@@deriving yojson]
  end

  module Response = struct
    type t = unit [@@deriving yojson]
  end

  module Handler = struct
    module Params = Params
    module Response = Response

    let handler =
      Protocol.HType.Immediate
        (fun ~token { Params.debug; root } ->
          Shell.set_workspace ~token ~debug ~root)
  end
end

(** [toc { uri } ] returns the table of contents for a document; the semantics
    are quite Coq-specific, in particular, each sentence of the document can
    contribute *)
module TableOfContents = struct
  let method_ = "petanque/toc"

  module Params = struct
    type t = { uri : Lsp.JLang.LUri.File.t } [@@deriving yojson]
  end

  module Response = struct
    type t = (string * Lsp.JLang.Ast.Info.t list option) list
    [@@deriving yojson]
  end

  module Handler = struct
    module Params = Params
    module Response = Response

    let handler =
      Protocol.HType.FullDoc
        { uri_fn = (fun { Params.uri } -> uri)
        ; handler = (fun ~token ~doc _ -> Shell.get_toc ~token ~doc)
        }
  end
end
