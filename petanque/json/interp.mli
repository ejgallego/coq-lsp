(************************************************************************)
(* Coq Petanque                                                         *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2019-2024 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(************************************************************************)

(* API for embedding petanque into a different protocol, needs to be moved to a
   core request library *)
module Action : sig
  type t =
    | Now of (token:Coq.Limits.Token.t -> (Yojson.Safe.t, string) Request.R.t)
    | Doc of
        { uri : Lang.LUri.File.t
        ; handler :
               token:Coq.Limits.Token.t
            -> doc:Fleche.Doc.t
            -> (Yojson.Safe.t, string) Request.R.t
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
val of_pet_err : ('a, Petanque.Agent.Error.t) result -> ('a, string) Request.R.t

(* Mostly Internal for pet-shell extensions; not for public consumption *)
val do_request :
     (module Protocol.Request.S)
  -> params:(string * Yojson.Safe.t) list
  -> Action.t
