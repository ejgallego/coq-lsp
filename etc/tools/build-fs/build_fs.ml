(* $ rm -rf kk && dune exec -- ./etc/tools/build-fs/build_fs.exe $(opam var lib)
   _build/install/default/lib/rocq-runtime _build/install/default/lib/coq kk *)

let ( / ) = Filename.concat

let concat_list base dirs =
  List.fold_left (fun path dir -> Filename.concat path dir) base dirs

module Path : sig
  type t = string

  val make : string -> t
  val exists : t -> bool
  val mkdir : t -> unit
  val relative : t -> string list -> t
  val pp : Format.formatter -> t -> unit
end = struct
  type t = string

  let make x = x
  let relative = concat_list
  let exists = Sys.file_exists
  let mkdir d = Sys.mkdir d 0o755
  let pp = Format.pp_print_string
end

let _readdir_full_paths ~dir =
  Sys.readdir dir |> Array.map Filename.(concat dir) |> Array.to_list

(* Check if the file is a directory *)
let check_dir ~dir f =
  if Sys.is_directory (dir / f) then Either.Left f else Right f

let filter_dir ~dir ~f entries =
  let sd, files = List.partition_map (fun d -> check_dir ~dir d) entries in
  let files = List.filter f files in
  (sd, files)

(* This returns the results without dir attached, so we can remap them *)
let scan_dir ~f ~dir =
  let base_dir = dir in
  let rec aux prefix =
    let p = List.rev prefix in
    let pstr = Path.relative "" p in
    let dir = Path.relative base_dir p in
    let subdirs, files_in_dir =
      Sys.readdir dir |> Array.to_list |> filter_dir ~dir ~f
    in
    let files = List.map (fun f -> Path.(relative pstr [ f ])) files_in_dir in
    files @ List.concat_map (fun sd -> aux (sd :: prefix)) subdirs
  in
  aux []

module Rocq_config = struct
  type t =
    { opam_root : Path.t
    ; rocq_root : Path.t
    ; rocqlib : Path.t
    }

  let make () =
    let opam_root = Path.make Sys.argv.(1) in
    let rocq_root = Path.make Sys.argv.(2) in
    let rocqlib = Path.make Sys.argv.(3) in
    { opam_root; rocq_root; rocqlib }
end

let error args =
  Format.kfprintf
    (fun fmt ->
      Format.fprintf fmt "@\n%!";
      exit 1)
    Format.err_formatter args

(* command with format and error check *)
let command cmd =
  Format.ksprintf
    (fun cmd ->
      let ev = Sys.command cmd in
      if ev <> 0 then error "Error for command: %s" cmd)
    cmd

let debug = false

module Entry = struct
  type t =
    { src : Path.t
    ; dst : Path.t
    }

  let copy_file src dst =
    let dst_dir = Filename.dirname dst in

    if not (Sys.file_exists dst_dir) then command "mkdir -p %s" dst_dir;

    command "cp -H %s %s" src dst

  (* "safe" copy function *)
  let copy ~dir { src; dst } =
    (* All files have a leading / *)
    let dst = dir ^ dst in
    if not (Path.exists src) then
      error "[Entry.copy] source file not found: %a" Path.pp src
    else if Path.exists dst then
      error "[Entry.copy] destination file exists: %a" Path.pp src
    else (
      if debug then Format.eprintf "copy %a to %a@\n" Path.pp src Path.pp dst;
      copy_file src dst)
end

(** output config:

    - /static/lib = ocamlpath
    - /static/rocq/theories *)

(* List of META files we need to copy, TODO: compute this list using
   ocamlfind *)
let meta_libs =
  [ "str"
  ; "seq"
  ; "uri"
  ; "base"
  ; "unix"
  ; "zarith"
  ; "yojson"
  ; "findlib"
  ; "dynlink"
  ; "parsexp"
  ; "sexplib"
  ; "sexplib0"
  ; "bigarray"
  ; "cmdliner"
  ; "ppx_hash"
  ; "angstrom"
  ; "stringext"
  ; "ppx_compare"
  ; "ppx_deriving"
  ; "ppx_sexp_conv"
  ; "memprof-limits"
  ; "ppx_deriving_yojson"
  ]

(* Already linked libraries *)
let find_meta ~config:{ Rocq_config.opam_root; _ } =
  let meta_entry lib =
    let src = Path.relative opam_root [ lib; "META" ] in
    let dst = Path.relative "/" [ "static"; "lib"; lib; "META" ] in
    { Entry.src; dst }
  in
  List.map meta_entry meta_libs

let make_entry ~oldbase ~newbase file =
  let src = oldbase / file in
  let dst = newbase / file in
  { Entry.src; dst }

let build_entries ~oldbase ~newbase ?pat () =
  let f _ = true in
  let files = scan_dir ~f ~dir:oldbase in
  let files =
    match pat with
    | Some pat ->
      let pat_filter f = Str.string_match pat f 0 in
      List.filter pat_filter files
    | None -> files
  in
  if debug then
    Format.eprintf "@[<v>%a@]@\n%!"
      Format.(pp_print_list ~pp_sep:pp_print_cut pp_print_string)
      files;
  List.map (make_entry ~oldbase ~newbase) files

let find_plugins ~config:{ Rocq_config.rocq_root; _ } =
  (* Rocq plugins *)
  let pat = Str.regexp "plugins/.*/.*.cma\\|META" in
  let rocq_entries =
    build_entries ~oldbase:rocq_root ~newbase:"/static/lib/rocq-runtime/" ~pat
      ()
  in
  (* Serlib plugins *)
  let serlib_root = "_build/install/default/lib/coq-lsp/" in
  let pat = Str.regexp "serlib/.*/.*.cma\\|META" in
  let serlib_entries =
    build_entries ~oldbase:serlib_root ~newbase:"/static/lib/coq-lsp/" ~pat ()
  in
  let wp_root = "_build/install/default/lib/coq-waterproof/" in
  let pat = Str.regexp "plugin/.*.cma\\|META" in
  let waterproof_entries =
    build_entries ~oldbase:wp_root ~newbase:"/static/lib/coq-waterproof/" ~pat
      ()
  in
  rocq_entries @ serlib_entries @ waterproof_entries

let find_vo ~config:{ Rocq_config.rocqlib; _ } =
  let pat = Str.regexp ".*" in
  let oldbase = rocqlib / "theories" in
  let corelib =
    build_entries ~oldbase ~newbase:"/static/rocqlib/theories/" ~pat ()
  in
  let oldbase = rocqlib / "user-contrib" in
  let user_contrib =
    build_entries ~oldbase ~newbase:"/static/rocqlib/user-contrib/" ~pat ()
  in
  corelib @ user_contrib

let check_output_dir ~dir =
  if Path.exists dir then error "Output directory %a already exists" Path.pp dir

let build ~dir (files : Entry.t list) =
  check_output_dir ~dir;
  Path.mkdir dir;
  List.iter (Entry.copy ~dir) files

(* Not possible until 4.14 due to zipc deps... zipc doesn't use dune so we can't
   vendor it :S *)
let compress ~dir:_ = ()

let find_pt () =
  { Entry.src = "etc/META.threads"; dst = "/static/lib/threads/META" }

let main () =
  let dir = Path.make Sys.argv.(4) in
  let config = Rocq_config.make () in
  let pt = find_pt () in
  let meta_files = find_meta ~config in
  let plugins = find_plugins ~config in
  let vo = find_vo ~config in
  let all_files = (pt :: meta_files) @ plugins @ vo in
  build ~dir all_files;
  compress ~dir;
  ()

let () =
  Printexc.record_backtrace true;
  if Array.length Sys.argv < 5 then
    error
      "Error: not enough args. Format is:@\n\
      \ build_fs opam_root rocq-runtime_root roqlib output_dir"
  else main ()
