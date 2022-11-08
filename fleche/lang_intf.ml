(************************************************************************)
(* Flèche Document Manager                                              *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2019-2022 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

module type S = sig
  (* XXX: ejgallego, do we start lines at 0? *)
  module Point : sig
    type t =
      { line : int
      ; character : int
      ; offset : int
      }
  end

  module Range : sig
    type t =
      { start : Point.t
      ; _end : Point.t
      }
  end

  (* Remove in favor of Range directly (however that's a bit annoying due to
     thep pervasive occurence of native locs usually; moreover a loc in Coq
     includes the file / dirpath *)
  module Loc : sig
    type t

    (* Difference between two locs *)
    type offset

    val initial : uri:string -> t
    val offset : t -> t -> offset
    val apply_offset : offset -> t -> t
    val to_range : t -> Range.t
  end

  module Pp : sig
    type t

    val to_string : t -> string
    val str : string -> t
  end

  module Message : sig
    type t = Loc.t option * int * Pp.t
  end

  module Ast : sig
    type t

    (* Single identifier *)
    module Id : sig
      type t

      val to_string : t -> string
    end

    (* Qualified Identifier *)
    module QualId : sig
      type t
    end

    val hash : t -> int
    val loc : t -> Loc.t option
    val compare : t -> t -> int
    val print : t -> Pp.t
    val grab_definitions : (Loc.t -> Id.t -> 'a) -> t list -> 'a list

    module View : sig
      type ast = t

      type t =
        (* This could be also extracted from the interpretation *)
        | Open of unit
        | End of unit
        | Require of
            { prefix : QualId.t option
            ; refs : QualId.t list
            }
        | Other

      val kind : ast -> t
    end

    val marshal_in : in_channel -> t
    val marshal_out : out_channel -> t -> unit
  end

  module Parse : sig
    module State : sig
      type t
    end

    module Parsable : sig
      type t

      val make : ?loc:Loc.t -> char Gramlib.Stream.t -> t
    end

    module Proof_mode : sig
      type t
    end

    val parse : State.t -> Proof_mode.t option -> Parsable.t -> Ast.t option
    val discard_to_dot : Parsable.t -> unit
  end

  module State : sig
    type t

    val compare : t -> t -> int
    val mode : st:t -> Parse.Proof_mode.t option
    val parsing : st:t -> Parse.State.t
    val drop_proofs : st:t -> t
    val in_state : st:t -> f:('a -> 'b) -> 'a -> 'b

    module Proof : sig
      type proof = Vernacstate.LemmaStack.t

      val get : st:t -> proof option
    end

    module Marshal : sig
      val read : in_channel -> t
      val write : out_channel -> t -> unit
    end
  end

  module Protect : sig
    type error = Loc.t option * Pp.t

    module R : sig
      type 'a t =
        | Completed of ('a, error) result
        | Interrupted (* signal sent, eval didn't complete *)
    end

    val eval : f:('i -> 'o) -> 'i -> 'o R.t

    (** Update the loc stored in the result, this is used by our cache-aware
        location *)
    val map_loc : f:(Loc.t -> Loc.t) -> 'a R.t -> 'a R.t
  end

  module Interp : sig
    module Info : sig
      type 'a t =
        { res : 'a
        ; feedback : Message.t list
        }
    end

    type 'a interp_result = 'a Info.t Protect.R.t

    val interp :
         st:State.t
      -> fb_queue:Message.t list ref
      -> Ast.t
      -> State.t interp_result

    val marshal_in : (in_channel -> 'a) -> in_channel -> 'a interp_result

    val marshal_out :
      (out_channel -> 'a -> unit) -> out_channel -> 'a interp_result -> unit
  end

  module Init : sig
    type opts =
      { msg_handler : Message.t -> unit
            (** callback to handle async messages from the lange engine *)
      ; load_module : string -> unit  (** callback to load cma/cmo files *)
      ; load_plugin : Mltop.PluginSpec.t -> unit
            (** callback to load findlib packages *)
      ; debug : bool  (** Enable Coq Debug mode *)
      }

    val init : opts -> State.t

    module Doc : sig
      type require_decl =
        string * string option * Vernacexpr.export_with_cats option

      type env =
        { vo_load_path : Loadpath.vo_path list
        ; ml_load_path : string list
        ; requires : require_decl list
        }

      val make :
        root_state:State.t -> env:env -> name:Names.DirPath.t -> State.t
    end
  end
end
