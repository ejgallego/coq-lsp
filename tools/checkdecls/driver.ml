(************************************************************************)
(* Flèche => checkdecls support for Proof blueprint                     *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2019-2024 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Andrej Bauaer, Emilio J. Gallego Arias                   *)
(************************************************************************)

(* Notes:

   - we could at some point use LSP, workspace/symbols seems like the closest
   call, then we could filter client-side *)

module Config = struct
  type t =
    { error_debug : bool
          (* Print extra information when a constant is not found *)
    }
end

let config : Config.t = { error_debug = false }
let err_fmt = Format.err_formatter
let pf fmt = Format.kfprintf (fun fmt -> Format.pp_print_flush fmt ()) fmt
let out = pf Format.std_formatter

let coq_init ~debug =
  let load_module = Dynlink.loadfile in
  let load_plugin = Coq.Loader.plugin_handler None in
  Coq.Init.(
    coq_init { debug; load_module; load_plugin; vm = true; warnings = None })

let workspace_init ~token ~debug ~cmdline ~roots =
  let roots = if List.length roots < 1 then [ Sys.getcwd () ] else roots in
  let default = Coq.Workspace.default ~debug ~cmdline in
  ( default
  , List.map
      (fun dir -> (dir, Coq.Workspace.guess ~token ~cmdline ~debug ~dir))
      roots )

(* Stdlib.Int.max requires OCaml 4.13 *)
let int_max x y = if x >= y then x else y
let max = List.fold_left int_max 0

(* We capture all the exns, bad people *)
let locate_decl decl =
  try
    let qid = Libnames.qualid_of_string decl in
    Ok (Nametab.locate_constant qid)
  with
  | Not_found -> Error (Format.asprintf "%s not found in name table" decl)
  | exn ->
    let iexn = Exninfo.capture exn in
    let exn_msg = CErrors.iprint iexn |> Pp.string_of_ppcmds in
    Error (Format.asprintf "internal Coq error: %s" exn_msg)

let pp_lp = function
  | Loadpath.Error.LibNotFound -> "LibNotFound"
  | Loadpath.Error.LibUnmappedDir -> "LibUnmappedDir"

(* EJGA: also check if the location info is available *)
let location_enabled = false

let do_decl decl =
  let open Coq.Compat.Result.O in
  let* cr = locate_decl decl in
  if location_enabled then
    let dp = Names.Constant.modpath cr |> Names.ModPath.dp in
    let* m = Coq.Module.make dp |> Result.map_error pp_lp in
    let id = Names.Constant.label cr |> Names.Label.to_string in
    let* _loc_info = Coq.Module.find m id in
    Ok ()
  else Ok ()

let do_decl decl =
  (* pf err "decl for: %s" decl; *)
  match do_decl decl with
  | Ok () ->
    (* pf err "decl found! %s" decl; *)
    0
  | Error err ->
    out "%s is missing.@\n" decl;
    if config.error_debug then
      pf err_fmt "Error when processing input %s [%s]@\n" decl err;
    1

let do_decls file =
  Coq.Compat.Ocaml_414.In_channel.(with_open_text file input_all)
  |> String.split_on_char '\n'
  |> List.filter (fun s -> not (CString.is_empty s))
  |> List.map do_decl |> max

let do_decls ws files =
  let intern = Vernacinterp.fs_intern in
  let uri =
    Lang.LUri.(of_string "file:///fake.v" |> File.of_uri) |> Result.get_ok
  in
  let () = Coq.Workspace.apply ~intern ~uri ws in
  List.map do_decls files

let do_decls ~token st ws files =
  let f files = do_decls ws files in
  Coq.State.in_state ~token ~st ~f files

let go ~cmdline ~roots ~debug ~files =
  Coq.Limits.select_best None;
  Coq.Limits.start ();
  let token = Coq.Limits.Token.create () in
  let root_state = coq_init ~debug in
  let default, _ws = workspace_init ~token ~debug ~cmdline ~roots in
  match do_decls ~token root_state default files with
  | { r = Interrupted; feedback = _ } -> 2
  | { r = Completed (Ok outs); feedback = _ } -> max outs
  | { r = Completed (Error _); feedback = _ } ->
    pf err_fmt "critical error!";
    222
