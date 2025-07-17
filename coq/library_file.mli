(*************************************************************************)
(* Copyright 2015-2019 MINES ParisTech -- Dual License LGPL 2.1+ / GPL3+ *)
(* Copyright 2019-2024 Inria           -- Dual License LGPL 2.1+ / GPL3+ *)
(* Copyright 2024-2025 Emilio J. Gallego Arias  -- LGPL 2.1+ / GPL3+     *)
(* Copyright 2025      CNRS                     -- LGPL 2.1+ / GPL3+     *)
(* Written by: Emilio J. Gallego Arias & coq-lsp contributors            *)
(*************************************************************************)
(* Rocq Language Server Protocol: .vo file API                           *)
(*************************************************************************)

(* API to handle vo libraries, we cannot use Library as module name due to Coq's
   libs not being wrapped... *)

(* Library stored in a .vo file, it can contain several modules *)
type t

(** Logical path of the library *)
val name : t -> Names.DirPath.t

module Entry : sig
  type t =
    { name : string
    ; typ : Constr.t
    ; file : string
    }
end

(** [toc libs] Returns the list of constants and inductives found on .vo
    libraries [libs], as pairs of [name, typ]. Note that the constants are
    returned in the order they appear on the file.

    NOTE that (unfortunately) this is a very expensive process, similary to
    Coq's Search, as this routine will have to traverse all the library objects
    in scope.

    Hence, we provide a slightly more efficient version that can do multiple
    libraries but with the same complexity.

    There have been several upstream Coq PRs trying to improve this situation,
    but so far they didn't make enough progress. *)
val toc :
     token:Limits.Token.t
  -> st:State.t
  -> t list
  -> (Entry.t list, Loc.t) Protect.E.t

(** Recovers the list of loaded libraries for state [st] *)
val loaded : token:Limits.Token.t -> st:State.t -> (t list, Loc.t) Protect.E.t

val locate_absolute_library : Names.DirPath.t -> (string, Exninfo.iexn) Result.t
