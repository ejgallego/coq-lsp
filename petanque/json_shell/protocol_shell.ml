open Petanque_json

(* set_workspace RPC *)
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

    module Response = struct
      type t = unit [@@deriving yojson]
    end

    let handler =
      Protocol.HType.Immediate
        (fun ~token { Params.debug; root } ->
          Shell.set_workspace ~token ~debug ~root)
  end
end
