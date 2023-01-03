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

module Setup = struct
  type t =
    { vo_load_path : Loadpath.vo_path list
    ; ml_include_path : string list
    ; require_libs :
        (string * string option * Vernacexpr.export_with_cats option) list
    ; indices_matter : bool
    ; impredicative_set : bool
    }

  let default ~implicit ~coqlib =
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
    let require_libs =
      [ ("Coq.Init.Prelude", None, Some (Lib.Import, None)) ]
    in
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
    }

  let append_loadpaths base ~vo_load_path ~ml_include_path =
    { base with
      vo_load_path = base.vo_load_path @ vo_load_path
    ; ml_include_path = base.ml_include_path @ ml_include_path
    }
end

type t = Setup.t * string
(* | CoqProject of Setup.t *)
(* | Dune *)

let rec parse_args args init w =
  match args with
  | [] -> (init, w)
  | "-indices-matter" :: rest ->
    parse_args rest init { w with Setup.indices_matter = true }
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

let apply ~libname
    ( { Setup.vo_load_path
      ; ml_include_path
      ; require_libs
      ; indices_matter
      ; impredicative_set
      ; _
      }
    , _ ) =
  Global.set_indices_matter indices_matter;
  Global.set_impredicative_set impredicative_set;
  List.iter Mltop.add_ml_dir ml_include_path;
  List.iter Loadpath.add_vo_path vo_load_path;
  Declaremods.start_library libname;
  load_objs require_libs

let loadpath_from_coqproject ~coqlib : Setup.t =
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
  let workspace = Setup.default ~coqlib ~implicit in
  let init, workspace = parse_args args true workspace in
  let workspace =
    if not init then { workspace with require_libs = [] } else workspace
  in
  Setup.append_loadpaths workspace ~vo_load_path ~ml_include_path

(* We append the default loadpath, TODO, support -noinit *)
let guess ~coqlib ~cmdline =
  if Sys.file_exists "_CoqProject" then
    ( loadpath_from_coqproject ~coqlib
    , Filename.concat (Sys.getcwd ()) "_CoqProject" )
  else (cmdline, "Command-line arguments")
