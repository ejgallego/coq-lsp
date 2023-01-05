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
  { vo_load_path : Loadpath.vo_path list
  ; ml_include_path : string list
  ; require_libs :
      (string * string option * Vernacexpr.export_with_cats option) list
  ; indices_matter : bool
  ; impredicative_set : bool
  ; kind : string
  }

let default ~implicit ~coqlib ~kind =
  let mk_path prefix = coqlib ^ "/" ^ prefix in
  let mk_lp ~ml ~root ~dir ~implicit =
    { Loadpath.unix_path = mk_path dir
    ; coq_path = root
    ; has_ml = ml
    ; implicit
    ; recursive = true
    }
  in
  let coq_root = Names.DirPath.make [ Libnames.coq_root ] in
  let default_root = Libnames.default_root_prefix in
  let require_libs = [ ("Coq.Init.Prelude", None, Some (Lib.Import, None)) ] in
  { vo_load_path =
      [ mk_lp ~ml:false ~root:coq_root ~implicit ~dir:"theories"
      ; mk_lp ~ml:true ~root:default_root ~implicit:false ~dir:"user-contrib"
      ]
  ; ml_include_path =
      (let unix_path = Filename.concat coqlib "../coq-core/plugins" in
       System.all_subdirs ~unix_path |> List.map fst)
  ; require_libs
  ; indices_matter = false
  ; impredicative_set = false
  ; kind
  }

let add_loadpaths base ~vo_load_path ~ml_include_path =
  { base with
    vo_load_path = base.vo_load_path @ vo_load_path
  ; ml_include_path = base.ml_include_path @ ml_include_path
  }

let describe { kind; vo_load_path; ml_include_path; require_libs; _ } =
  let require_msg =
    String.concat " " (List.map (fun (s, _, _) -> s) require_libs)
  in
  let n_vo = List.length vo_load_path in
  let n_ml = List.length ml_include_path in
  Format.asprintf
    "@[Configuration loaded from %s@\n\
     - Modules [%s] will be loaded by default; %d Coq path directory bindings \
     in scope; %d Coq plugin directory bindings in scope@]"
    kind require_msg n_vo n_ml

let rec parse_args args init w =
  match args with
  | [] -> (init, w)
  | "-indices-matter" :: rest ->
    parse_args rest init { w with indices_matter = true }
  | "-impredicative-nset" :: rest ->
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

(* NOTE: Use exhaustive match below to avoid bugs by skipping fields *)
let apply ~libname
    { vo_load_path
    ; ml_include_path
    ; require_libs
    ; indices_matter
    ; impredicative_set
    ; kind = _
    } =
  Global.set_indices_matter indices_matter;
  Global.set_impredicative_set impredicative_set;
  List.iter Mltop.add_ml_dir ml_include_path;
  List.iter Loadpath.add_vo_path vo_load_path;
  Declaremods.start_library libname;
  load_objs require_libs

let workspace_from_coqproject ~coqlib : t =
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
    read_project_file ~warning_fn:(fun _ -> ()) "_CoqProject"
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
  let workspace = default ~coqlib ~implicit ~kind in
  let init, workspace = parse_args args true workspace in
  let workspace =
    if not init then { workspace with require_libs = [] } else workspace
  in
  add_loadpaths workspace ~vo_load_path ~ml_include_path

module CmdLine = struct
  type t =
    { coqlib : string
    ; vo_load_path : Loadpath.vo_path list
    ; ml_include_path : string list
    }
end

let workspace_from_cmdline { CmdLine.coqlib; vo_load_path; ml_include_path } =
  let kind = "Command-line arguments" in
  let implicit = true in
  let w = default ~implicit ~coqlib ~kind in
  add_loadpaths w ~vo_load_path ~ml_include_path

let guess ~cmdline =
  if Sys.file_exists "_CoqProject" then
    workspace_from_coqproject ~coqlib:cmdline.CmdLine.coqlib
  else workspace_from_cmdline cmdline
