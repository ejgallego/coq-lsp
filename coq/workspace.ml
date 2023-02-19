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
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2019-2022 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

type t =
  { coqlib : string
  ; coqcorelib : string
  ; vo_load_path : Loadpath.vo_path list
  ; ml_include_path : string list
  ; require_libs :
      (string * string option * Vernacexpr.export_with_cats option) list
  ; indices_matter : bool
  ; impredicative_set : bool
  ; kind : string
  ; debug : bool
  }

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

let default ~implicit ~coqcorelib ~coqlib ~kind ~debug =
  let coqcorelib = getenv "COQCORELIB" coqcorelib in
  let coqlib = getenv "COQLIB" coqlib in
  let mk_path_coqlib prefix = coqlib ^ "/" ^ prefix in
  (* Setup ml_include for the core plugins *)
  let ml_include_path =
    let unix_path = Filename.concat coqcorelib "plugins" in
    System.all_subdirs ~unix_path |> List.map fst
  in
  (* Setup vo_include path, note that has_ml=true does the job for user_contrib
     and plugins *)
  let userpaths = mk_path_coqlib "user-contrib" :: Envars.coqpath in
  let user_vo_path = List.map mk_userlib userpaths in
  let stdlib_vo_path = mk_path_coqlib "theories" |> mk_stdlib ~implicit in
  let vo_load_path = stdlib_vo_path :: user_vo_path in
  let require_libs = [ ("Coq.Init.Prelude", None, Some (Lib.Import, None)) ] in
  { coqlib
  ; coqcorelib
  ; vo_load_path
  ; ml_include_path
  ; require_libs
  ; indices_matter = false
  ; impredicative_set = false
  ; kind
  ; debug
  }

let add_loadpaths base ~vo_load_path ~ml_include_path =
  { base with
    vo_load_path = base.vo_load_path @ vo_load_path
  ; ml_include_path = base.ml_include_path @ ml_include_path
  }

let pp_load_path fmt
    { Loadpath.unix_path; coq_path; implicit = _; has_ml = _; recursive = _ } =
  Format.fprintf fmt "Path %s ---> %s"
    (Names.DirPath.to_string coq_path)
    unix_path

let describe { coqlib; kind; vo_load_path; ml_include_path; require_libs; _ } =
  let require_msg =
    String.concat " " (List.map (fun (s, _, _) -> s) require_libs)
  in
  let n_vo = List.length vo_load_path in
  let n_ml = List.length ml_include_path in
  let extra =
    Format.asprintf "@[vo_paths:@\n @[<v>%a@]@\nml_paths:@\n @[<v>%a@]@]"
      (Format.pp_print_list pp_load_path)
      vo_load_path
      Format.(pp_print_list pp_print_string)
      ml_include_path
  in
  ( Format.asprintf
      "@[Configuration loaded from %s@\n\
      \ - coqlib is at: %s@\n\
      \ - Modules [%s] will be loaded by default@\n\
      \ - %d Coq path directory bindings in scope; %d Coq plugin directory \
       bindings in scope@]"
      kind coqlib require_msg n_vo n_ml
  , extra )

let rec parse_args args init w =
  match args with
  | [] -> (init, w)
  | "-indices-matter" :: rest ->
    parse_args rest init { w with indices_matter = true }
  | "-impredicative-set" :: rest ->
    parse_args rest init { w with impredicative_set = true }
  | "-noinit" :: rest -> parse_args rest false w
  | _ :: rest ->
    (* emit warning? *)
    parse_args rest init w

(* Require a set of libraries *)
let load_objs libs =
  let rq_file (dir, from, exp) =
    let mp = Libnames.qualid_of_string dir in
    let mfrom = Option.map Libnames.qualid_of_string from in
    Flags.silently
      (Vernacentries.vernac_require mfrom exp)
      [ (mp, Vernacexpr.ImportAll) ]
  in
  List.(iter rq_file (rev libs))

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
    try Filename.chop_extension (Filename.basename f)
    with Invalid_argument _ -> f
  in
  let id = Names.Id.of_string f in
  let ldir = Libnames.add_dirpath_suffix ldir0 id in
  ldir

(* This is a bit messy upstream, as -I both extends Coq loadpath and OCAMLPATH
   loadpath *)
let findlib_init ~ml_include_path =
  let env_ocamlpath = try [ Sys.getenv "OCAMLPATH" ] with Not_found -> [] in
  let env_ocamlpath = ml_include_path @ env_ocamlpath in
  let ocamlpathsep = if Sys.unix then ":" else ";" in
  let env_ocamlpath = String.concat ocamlpathsep env_ocamlpath in
  Findlib.init ~env_ocamlpath ()

(* NOTE: Use exhaustive match below to avoid bugs by skipping fields *)
let apply ~uri
    { coqlib = _
    ; coqcorelib = _
    ; vo_load_path
    ; ml_include_path
    ; require_libs
    ; indices_matter
    ; impredicative_set
    ; kind = _
    ; debug
    } =
  if debug then CDebug.set_flags "backtrace";
  Global.set_indices_matter indices_matter;
  Global.set_impredicative_set impredicative_set;
  List.iter Mltop.add_ml_dir ml_include_path;
  findlib_init ~ml_include_path;
  List.iter Loadpath.add_vo_path vo_load_path;
  Declaremods.start_library (dirpath_of_uri ~uri);
  load_objs require_libs

let workspace_from_coqproject ~coqcorelib ~coqlib ~debug cp_file : t =
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
    ; coq_path = Libnames.dirpath_of_string coq_path
    }
  in
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
  let implicit = true in
  let kind = Filename.concat (Sys.getcwd ()) "_CoqProject" in
  let workspace = default ~coqlib ~coqcorelib ~implicit ~kind ~debug in
  let init, workspace = parse_args args true workspace in
  let workspace =
    if not init then { workspace with require_libs = [] } else workspace
  in
  add_loadpaths workspace ~vo_load_path ~ml_include_path

module CmdLine = struct
  type t =
    { coqlib : string
    ; coqcorelib : string
    ; vo_load_path : Loadpath.vo_path list
    ; ml_include_path : string list
    }
end

let workspace_from_cmdline ~debug
    { CmdLine.coqlib; coqcorelib; vo_load_path; ml_include_path } =
  let kind = "Command-line arguments" in
  let implicit = true in
  let w = default ~implicit ~coqcorelib ~coqlib ~kind ~debug in
  add_loadpaths w ~vo_load_path ~ml_include_path

let guess ~debug ~cmdline ~dir =
  let cp_file = Filename.concat dir "_CoqProject" in
  if Sys.file_exists cp_file then
    let { CmdLine.coqlib; coqcorelib; _ } = cmdline in
    workspace_from_coqproject ~coqcorelib ~coqlib ~debug cp_file
  else workspace_from_cmdline ~debug cmdline
