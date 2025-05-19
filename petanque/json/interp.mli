(************************************************************************)
(* Coq Petanque                                                         *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2019-2024 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(************************************************************************)

(* Payload specialized to json / string *)
type json_rpc_result = (Yojson.Safe.t, string) Request.R.t

(* API for embedding petanque into a different protocol, needs to be moved to a
   core request library *)
module Action : sig
  type t =
    | Now of (token:Coq.Limits.Token.t -> json_rpc_result)
    | Doc of
        { uri : Lang.LUri.File.t
        ; handler :
            token:Coq.Limits.Token.t -> doc:Fleche.Doc.t -> json_rpc_result
        }
end

type 'a handle = token:Coq.Limits.Token.t -> Action.t -> 'a

val handle_request :
     do_handle:'a handle
  -> unhandled:(token:Coq.Limits.Token.t -> method_:string -> 'a)
  -> token:Coq.Limits.Token.t
  -> method_:string
  -> params:(string * Yojson.Safe.t) list
  -> 'a

(* aux function, XXX: fixme to include feedback *)
val of_pet_err :
  ('a, Petanque.Agent.Error.t) Request.R.t -> ('a, string) Request.R.t

(* Mostly Internal for pet-shell extensions; not for public consumption *)
val do_request :
     (module Protocol.Request.S)
  -> params:(string * Yojson.Safe.t) list
  -> Action.t
