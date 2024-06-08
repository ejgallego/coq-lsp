open JAgent

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
    type t = int [@@deriving yojson]
  end

  module Handler = struct
    module Params = Params

    module Response = struct
      type t = Env.t [@@deriving yojson]
    end

    let handler ~token { Params.debug; root } =
      Petanque.Shell.set_workspace ~token ~debug ~root
  end
end
