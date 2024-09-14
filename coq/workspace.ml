(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(************************************************************************)
(* Coq Language Server Protocol                                         *)
(* Copyright 2016-2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+ *)
(* Copyright 2019-2024 Inria           -- Dual License LGPL 2.1 / GPL3+ *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

module Flags_ = Flags

module Flags = struct
  type t =
    { impredicative_set : bool
    ; indices_matter : bool
    ; type_in_type : bool
    ; rewrite_rules : bool
    }

  let default =
    { impredicative_set = false
    ; indices_matter = false
    ; type_in_type = false
    ; rewrite_rules = false
    }

  let apply { impredicative_set; indices_matter; type_in_type; rewrite_rules } =
    Global.set_impredicative_set impredicative_set;
    Global.set_indices_matter indices_matter;
    Global.set_check_universes (not type_in_type);
    Global.set_rewrite_rules_allowed rewrite_rules
end

module Warning : sig
  type t

  val make : string -> t

  (** Adds new warnings to the list of current warnings *)
  val apply : t list -> unit
end = struct
  type t = string

  let make x = x

  let apply w =
    let old_warn = CWarnings.get_flags () in
    let new_warn = String.concat "," w in
    CWarnings.set_flags (old_warn ^ "," ^ new_warn)
end

module Require = struct
  type t =
    { library : string
    ; from : string option
    ; flags : Vernacexpr.export_with_cats option
    }
end

type t =
  { coqlib : string
  ; coqcorelib : string
  ; ocamlpath : string option
  ; vo_load_path : Loadpath.vo_path list
  ; ml_include_path : string list
  ; require_libs : Require.t list
  ; flags : Flags.t
  ; warnings : Warning.t list
  ; kind : string
  ; debug : bool
  }

let inject_requires ~extra_requires (ws : t) =
  { ws with require_libs = ws.require_libs @ extra_requires }

let hash = Hashtbl.hash
let compare = Stdlib.compare

(* Lib setup, XXX unify with sysinit *)
let coq_root = Names.DirPath.make [ Libnames.coq_root ]
let default_root = Libnames.default_root_prefix

let mk_lp ~has_ml ~coq_path ~unix_path ~implicit =
  { Loadpath.unix_path; coq_path; has_ml; implicit; recursive = true }

let mk_stdlib ~implicit unix_path =
  mk_lp ~has_ml:false ~coq_path:coq_root ~implicit ~unix_path

let mk_userlib unix_path =
  mk_lp ~has_ml:true ~coq_path:default_root ~implicit:false ~unix_path

let getenv var else_ = try Sys.getenv var with Not_found -> else_

let rec parse_args args init boot libs f w =
  match args with
  | [] -> (init, boot, List.rev libs, f, List.rev w)
  | "-rifrom" :: from :: lib :: rest ->
    parse_args rest init boot ((Some from, lib) :: libs) f w
  | "-impredicative-set" :: rest ->
    parse_args rest init boot libs { f with Flags.impredicative_set = true } w
  | "-indices-matter" :: rest ->
    parse_args rest init boot libs { f with Flags.indices_matter = true } w
  | "-type-in-type" :: rest ->
    parse_args rest init boot libs { f with Flags.type_in_type = true } w
  | "-allow-rewrite-rules" :: rest ->
    parse_args rest init boot libs { f with Flags.rewrite_rules = true } w
  | "-noinit" :: rest -> parse_args rest false boot libs f w
  | "-boot" :: rest -> parse_args rest init true libs f w
  | "-w" :: warn :: rest ->
    let warn = Warning.make warn in
    parse_args rest init boot libs f (warn :: w)
  | _ :: rest ->
    (* emit warning? *)
    parse_args rest init boot libs f w

module CmdLine = struct
  type t =
    { coqlib : string
    ; coqcorelib : string
    ; ocamlpath : string option
    ; vo_load_path : Loadpath.vo_path list
    ; ml_include_path : string list
    ; args : string list
    ; require_libraries : (string option * string) list
    }
end

let mk_require_from (from, library) =
  let flags = Some (Lib.Import, None) in
  { Require.library; from; flags }

let make ~cmdline ~implicit ~kind ~debug =
  let { CmdLine.coqcorelib
      ; coqlib
      ; ocamlpath
      ; args
      ; ml_include_path
      ; vo_load_path
      ; require_libraries
      } =
    cmdline
  in
  let coqcorelib = getenv "COQCORELIB" coqcorelib in
  let coqlib = getenv "COQLIB" coqlib in
  let mk_path_coqlib prefix = coqlib ^ "/" ^ prefix in
  let init, boot, libs, flags, warnings =
    parse_args args true false [] Flags.default []
  in
  (* Setup ml_include for the core plugins *)
  let dft_ml_include_path, dft_vo_load_path =
    if boot then ([], [])
    else
      let unix_path = Filename.concat coqcorelib "plugins" in
      ( System.all_subdirs ~unix_path |> List.map fst
      , (* Setup vo_include path, note that has_ml=true does the job for
           user_contrib and plugins *)
        let userpaths = mk_path_coqlib "user-contrib" :: Envars.coqpath in
        let user_vo_path = List.map mk_userlib userpaths in
        let stdlib_vo_path = mk_path_coqlib "theories" |> mk_stdlib ~implicit in
        stdlib_vo_path :: user_vo_path )
  in
  let require_libs =
    let rq_list =
      if init then ((None, "Stdlib.Init.Prelude") :: require_libraries) @ libs
      else require_libraries @ libs
    in
    List.map mk_require_from rq_list
  in
  let vo_load_path = dft_vo_load_path @ vo_load_path in
  let ml_include_path = dft_ml_include_path @ ml_include_path in
  { coqlib
  ; coqcorelib
  ; ocamlpath
  ; vo_load_path
  ; ml_include_path
  ; require_libs
  ; flags
  ; warnings
  ; kind
  ; debug
  }

let pp_load_path fmt
    { Loadpath.unix_path; coq_path; implicit = _; has_ml = _; recursive = _ } =
  Format.fprintf fmt "Path %s ---> %s"
    (Names.DirPath.to_string coq_path)
    unix_path

(* This is a bit messy upstream, as -I both extends Coq loadpath and OCAMLPATH
   loadpath *)
let findlib_init ~ml_include_path ~ocamlpath =
  let config, ocamlpath =
    match ocamlpath with
    | None -> (None, [])
    | Some dir -> (Some (Filename.concat dir "findlib.conf"), [ dir ])
  in
  let env_ocamlpath = try [ Sys.getenv "OCAMLPATH" ] with Not_found -> [] in
  let env_ocamlpath = ml_include_path @ env_ocamlpath @ ocamlpath in
  let ocamlpathsep = if Sys.unix then ":" else ";" in
  let env_ocamlpath = String.concat ocamlpathsep env_ocamlpath in
  Findlib.init ~env_ocamlpath ?config ()

let describe
    { coqlib
    ; coqcorelib
    ; ocamlpath
    ; kind
    ; vo_load_path
    ; ml_include_path
    ; require_libs
    ; flags = _
    ; warnings = _
    ; debug = _
    } =
  let require_msg =
    String.concat " "
      (List.map (fun { Require.library; _ } -> library) require_libs)
  in
  let n_vo = List.length vo_load_path in
  let n_ml = List.length ml_include_path in
  let ocamlpath_msg =
    Option.cata
      (fun op -> "was overrident to " ^ op)
      "wasn't overriden" ocamlpath
  in
  (* We need to do this in order for the calls to Findlib to make sense, but
     really need to modify this *)
  findlib_init ~ml_include_path ~ocamlpath;
  let fl_packages = Findlib.list_packages' () in
  let fl_config = Findlib.config_file () in
  let fl_location = Findlib.default_location () in
  let fl_paths = Findlib.search_path () in
  let extra =
    Format.asprintf
      "@[vo_paths:@\n\
      \ @[<v>%a@]@\n\
       ml_paths:@\n\
      \ @[<v>%a@]@\n\
       findlib_paths:@\n\
      \ @[<v>%a@]@\n\
       findlib_packages:@\n\
      \ @[<v>%a@]@]"
      (Format.pp_print_list pp_load_path)
      vo_load_path
      Format.(pp_print_list pp_print_string)
      ml_include_path
      Format.(pp_print_list pp_print_string)
      fl_paths
      Format.(pp_print_list pp_print_string)
      fl_packages
  in
  ( Format.asprintf
      "@[Configuration loaded from %s@\n\
      \ - coqlib is at: %s@\n\
      \   + coqcorelib is at: %s@\n\
      \ - Modules [%s] will be loaded by default@\n\
      \ - %d Coq path directory bindings in scope; %d Coq plugin directory \
       bindings in scope@\n\
      \ - ocamlpath %s@\n\
      \   + findlib config: %s@\n\
      \   + findlib default location: %s@]" kind coqlib coqcorelib require_msg
      n_vo n_ml ocamlpath_msg fl_config fl_location
  , extra )

let describe_guess = function
  | Ok w -> describe w
  | Error msg -> (msg, "")

(* Require a set of libraries *)
let load_objs ~intern libs =
  let rq_file { Require.library; from; flags } =
    let mp = Libnames.qualid_of_string library in
    let mfrom = Option.map Libnames.qualid_of_string from in
    Flags_.silently
      (Vernacentries.vernac_require ~intern mfrom flags)
      [ (mp, Vernacexpr.ImportAll) ]
  in
  List.(iter rq_file (rev libs))

let fleche_chop_extension basename =
  match Filename.chop_suffix_opt ~suffix:".v.tex" basename with
  | Some file -> file
  | None -> Filename.chop_extension basename

(* We need to compute this with the right load path *)
let dirpath_of_uri ~uri =
  let f = Lang.LUri.File.to_string_file uri in
  let ldir0 =
    try
      let lp = Loadpath.find_load_path (Filename.dirname f) in
      Loadpath.logical lp
    with Not_found -> Libnames.default_root_prefix
  in
  let f =
    try fleche_chop_extension (Filename.basename f)
    with Invalid_argument _ -> f
  in
  let id = Names.Id.of_string f in
  let ldir = Libnames.add_dirpath_suffix ldir0 id in
  ldir

(* NOTE: Use exhaustive match below to avoid bugs by skipping fields *)
let apply ~intern ~uri
    { coqlib = _
    ; coqcorelib = _
    ; ocamlpath
    ; vo_load_path
    ; ml_include_path
    ; require_libs
    ; flags
    ; warnings
    ; kind = _
    ; debug
    } =
  if debug then CDebug.set_flags "backtrace";
  Flags.apply flags;
  Warning.apply warnings;
  List.iter Mltop.add_ml_dir ml_include_path;
  findlib_init ~ml_include_path ~ocamlpath;
  List.iter Loadpath.add_vo_path vo_load_path;
  Declaremods.start_library (dirpath_of_uri ~uri);
  load_objs ~intern require_libs

(* This can raise, and will do in incorrect CoqProject files *)
let dirpath_of_string_exn coq_path = Libnames.dirpath_of_string coq_path

let workspace_from_coqproject ~cmdline ~debug cp_file : t =
  (* Io.Log.error "init" "Parsing _CoqProject"; *)
  let open CoqProject_file in
  let to_vo_loadpath f implicit =
    let open Loadpath in
    let unix_path, coq_path = f in
    (* Lsp.Io.log_error "init"
     *   (Printf.sprintf "Path from _CoqProject: %s %s" unix_path.path coq_path); *)
    { implicit
    ; recursive = true
    ; has_ml = false
    ; unix_path = unix_path.path
    ; coq_path = dirpath_of_string_exn coq_path
    }
  in
  (* XXX: [read_project_file] will do [exit 1] on parsing error! Please someone
     fix upstream!! *)
  let { r_includes; q_includes; ml_includes; extra_args; _ } =
    read_project_file ~warning_fn:(fun _ -> ()) cp_file
  in
  let ml_include_path = List.map (fun f -> f.thing.path) ml_includes in
  let vo_path = List.map (fun f -> to_vo_loadpath f.thing false) q_includes in
  let vo_load_path =
    List.append vo_path
      (List.map (fun f -> to_vo_loadpath f.thing true) r_includes)
  in
  let args = List.map (fun f -> f.thing) extra_args in
  let cmdline =
    CmdLine.
      { cmdline with
        args = cmdline.args @ args
      ; vo_load_path = cmdline.vo_load_path @ vo_load_path
      ; ml_include_path = cmdline.ml_include_path @ ml_include_path
      }
  in
  let implicit = true in
  let kind = cp_file in
  make ~cmdline ~implicit ~kind ~debug

let workspace_from_cmdline ~debug ~cmdline =
  let kind = "Command-line arguments" in
  let implicit = true in
  make ~cmdline ~implicit ~kind ~debug

let guess ~debug ~cmdline ~dir () =
  let cp_file = Filename.concat dir "_CoqProject" in
  if Sys.file_exists cp_file then
    workspace_from_coqproject ~cmdline ~debug cp_file
  else workspace_from_cmdline ~debug ~cmdline

let guess ~token ~debug ~cmdline ~dir =
  let { Protect.E.r; feedback } =
    Protect.eval ~token ~f:(guess ~debug ~cmdline ~dir) ()
  in
  ignore feedback;
  match r with
  | Protect.R.Interrupted -> Error "Workspace Scanning Interrupted"
  | Protect.R.Completed (Error (User (_, msg)))
  | Protect.R.Completed (Error (Anomaly (_, msg))) ->
    Error (Format.asprintf "Workspace Scanning Errored: %a" Pp.pp_with msg)
  | Protect.R.Completed (Ok workspace) -> Ok workspace

let default ~debug ~cmdline = workspace_from_cmdline ~debug ~cmdline
