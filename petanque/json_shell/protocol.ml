open Petanque

(* Serialization for agent types *)
open JAgent

(* RPC-side server mappings, internal; we could split this in a different module
   eventually as to make this clearer. *)
module type Handler = sig
  (* Server-side RPC specification *)
  module Params : sig
    type t [@@deriving of_yojson]
  end

  (* Server-side RPC specification *)
  module Response : sig
    type t [@@deriving to_yojson]
  end

  val handler : token:Coq.Limits.Token.t -> Params.t -> Response.t R.t
end

(* Note that here we follow JSON-RPC / LSP capitalization conventions *)
module Request = struct
  module type S = sig
    val method_ : string

    (* Protocol params specification *)
    module Params : sig
      type t [@@deriving yojson]
    end

    (* Protocol response specification *)
    module Response : sig
      type t [@@deriving yojson]
    end

    module Handler : Handler
  end
end

(* init RPC *)
module Init = struct
  let method_ = "petanque/init"

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

    let handler ~token { Params.debug; root } = Agent.init ~token ~debug ~root
  end
end

(* start RPC *)
module Start = struct
  let method_ = "petanque/start"

  module Params = struct
    type t =
      { env : int
      ; uri : Lsp.JLang.LUri.File.t
      ; pre_commands : string option [@default None]
      ; thm : string
      }
    [@@deriving yojson]
  end

  module Response = struct
    type t = int [@@deriving yojson]
  end

  module Handler = struct
    module Params = struct
      type t =
        { env : Env.t
        ; uri : Lsp.JLang.LUri.File.t
        ; pre_commands : string option [@default None]
        ; thm : string
        }
      [@@deriving yojson]
    end

    module Response = struct
      type t = State.t [@@deriving yojson]
    end

    let handler ~token { Params.env; uri; pre_commands; thm } =
      Agent.start ~token ~env ~uri ?pre_commands ~thm ()
  end
end

(* run_tac RPC *)
module RunTac = struct
  let method_ = "petanque/run"

  module Params = struct
    type t =
      { st : int
      ; tac : string
      }
    [@@deriving yojson]
  end

  module Response = struct
    type t = int Run_result.t [@@deriving yojson]
  end

  module Handler = struct
    module Params = struct
      type t =
        { st : State.t
        ; tac : string
        }
      [@@deriving yojson]
    end

    module Response = struct
      type t = State.t Run_result.t [@@deriving yojson]
    end

    let handler ~token { Params.st; tac } = Agent.run_tac ~token ~st ~tac
  end
end

(* goals RPC *)
module Goals = struct
  let method_ = "petanque/goals"

  module Params = struct
    type t = { st : int } [@@deriving yojson]
  end

  module Response = struct
    type t = Goals.t [@@deriving yojson]
  end

  module Handler = struct
    module Params = struct
      type t = { st : State.t } [@@deriving yojson]
    end

    module Response = Response

    let handler ~token { Params.st } = Agent.goals ~token ~st
  end
end

(* premises RPC *)
module Premises = struct
  let method_ = "petanque/premises"

  module Params = struct
    type t = { st : int } [@@deriving yojson]
  end

  module Response = struct
    type t = Premise.t list [@@deriving yojson]
  end

  module Handler = struct
    module Params = struct
      type t = { st : State.t } [@@deriving yojson]
    end

    module Response = Response

    let handler ~token { Params.st } = Agent.premises ~token ~st
  end
end

(* Notifications don't get a reply *)
module Notification = struct
  module type S = sig
    val method_ : string

    module Params : sig
      type t [@@deriving yojson]
    end
  end
end

(* These two are identical from LSP *)

(* Trace notification *)
module Trace = struct
  let method_ = "$/logTrace"

  module Params = struct
    type t =
      { message : string
      ; verbose : string option [@default None]
      }
    [@@deriving yojson]
  end

  let make params =
    let params = Params.to_yojson params |> Yojson.Safe.Util.to_assoc in
    Lsp.Base.Message.Notification { method_; params }
end

(* Message notification *)
module Message = struct
  let method_ = "window/logMessage"

  module Params = struct
    type t =
      { type_ : int [@key "type"]
      ; message : string
      }
    [@@deriving yojson]
  end

  let make params =
    let params = Params.to_yojson params |> Yojson.Safe.Util.to_assoc in
    Lsp.Base.Message.Notification { method_; params }
end
