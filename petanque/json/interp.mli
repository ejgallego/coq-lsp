(************************************************************************)
(* Coq Petanque                                                         *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2019-2024 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(************************************************************************)

(* API for embedding petanque into a different protocol, needs to be moved to a
   core request library *)
type 'a r = ('a, int * string) Result.t

module Action : sig
  type t =
    | Now of (token:Coq.Limits.Token.t -> Yojson.Safe.t r)
    | Doc of
        { uri : Lang.LUri.File.t
        ; handler :
            token:Coq.Limits.Token.t -> doc:Fleche.Doc.t -> Yojson.Safe.t r
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

(* aux function *)
val of_pet_err :
  ('a, Petanque.Agent.Error.t) result -> ('a, int * string) Result.t

(* Mostly Internal for pet-shell extensions; not for public consumption *)
val do_request :
     (module Protocol.Request.S)
  -> params:(string * Yojson.Safe.t) list
  -> Action.t
