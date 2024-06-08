open Petanque

let read_raw ~uri =
  let file = Lang.LUri.File.to_string_file uri in
  try Ok Coq.Compat.Ocaml_414.In_channel.(with_open_text file input_all)
  with Sys_error err -> Error (Agent.Error.Coq err)

let setup_doc ~io ~token env uri =
  match read_raw ~uri with
  | Ok raw ->
    let doc = Fleche.Doc.create ~token ~env ~uri ~version:0 ~raw in
    (* print_diags doc; *)
    let target = Fleche.Doc.Target.End in
    Ok (Fleche.Doc.check ~io ~token ~target ~doc ())
  | Error err -> Error err

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

    let env = ref None

    let handler ~token { Params.debug; root } =
      let res = Agent.set_workspace ~token ~debug ~root in
      Result.iter (fun env_ -> env := Some env_) res;
      res
  end
end

(* start RPC *)
module Start = struct
  let method_ = "petanque/start"

  module Params = struct
    type t =
      { uri : Lsp.JLang.LUri.File.t
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
        { uri : Lsp.JLang.LUri.File.t
        ; pre_commands : string option [@default None]
        ; thm : string
        }
      [@@deriving yojson]
    end

    module Response = struct
      type t = State.t [@@deriving yojson]
    end

    let handler ~token { Params.uri; pre_commands; thm } =
      let fn ~io uri =
        setup_doc ~io ~token (Option.get !SetWorkspace.Handler.env) uri
      in
      Agent.start ~token ~fn ~uri ?pre_commands ~thm ()
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
