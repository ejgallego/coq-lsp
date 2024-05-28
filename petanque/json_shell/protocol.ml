open Petanque

(* Serialization for agent types *)
open JAgent

(* Note that here we follow JSON-RPC / LSP capitalization conventions *)
module Request = struct
  module type S = sig
    val method_ : string

    (* Would be good to remove this duplicity, but that would complicate the
       server side setup which now is trivial. *)

    (* Server-side params specification *)
    module Params : sig
      type t [@@deriving of_yojson]
    end

    (* Client-side params specification *)
    module Params_ : sig
      type t [@@deriving to_yojson]
    end

    (* Server-side response specification *)
    module Response : sig
      type t [@@deriving to_yojson]
    end

    (* Client-side response specification *)
    module Response_ : sig
      type t [@@deriving of_yojson]
    end

    val handler : token:Coq.Limits.Token.t -> Params.t -> Response.t R.t
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

  module Params_ = Params

  module Response = struct
    type t = Env.t [@@deriving yojson]
  end

  module Response_ = struct
    type t = int [@@deriving yojson]
  end

  let handler ~token { Params.debug; root } = Agent.init ~token ~debug ~root
end

(* start RPC *)
module Start = struct
  let method_ = "petanque/start"

  module Params = struct
    type t =
      { env : Env.t
      ; uri : Lsp.JLang.LUri.File.t
      ; thm : string
      }
    [@@deriving yojson]
  end

  module Params_ = struct
    type t =
      { env : int
      ; uri : Lsp.JLang.LUri.File.t
      ; thm : string
      }
    [@@deriving yojson]
  end

  module Response = struct
    type t = State.t [@@deriving yojson]
  end

  module Response_ = struct
    type t = int [@@deriving yojson]
  end

  let handler ~token { Params.env; uri; thm } =
    Agent.start ~token ~env ~uri ~thm
end

(* run_tac RPC *)
module RunTac = struct
  let method_ = "petanque/run"

  module Params = struct
    type t =
      { st : State.t
      ; tac : string
      }
    [@@deriving yojson]
  end

  module Params_ = struct
    type t =
      { st : int
      ; tac : string
      }
    [@@deriving yojson]
  end

  module Response = struct
    type t = State.t [@@deriving yojson]
  end

  module Response_ = struct
    type t = int [@@deriving yojson]
  end

  let handler ~token { Params.st; tac } = Agent.run_tac ~token ~st ~tac
end

(* goals RPC *)
module Goals = struct
  let method_ = "petanque/goals"

  module Params = struct
    type t = { st : State.t } [@@deriving yojson]
  end

  module Params_ = struct
    type t = { st : int } [@@deriving yojson]
  end

  module Response = struct
    type t = Goals.t [@@deriving yojson]
  end

  module Response_ = Response

  let handler ~token { Params.st } = Agent.goals ~token ~st
end

(* premises RPC *)
module Premises = struct
  let method_ = "petanque/premises"

  module Params = struct
    type t = { st : State.t } [@@deriving yojson]
  end

  module Params_ = struct
    type t = { st : int } [@@deriving yojson]
  end

  module Response = struct
    type t = string list [@@deriving yojson]
  end

  module Response_ = Response

  let handler ~token { Params.st } = Agent.premises ~token ~st
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
end
