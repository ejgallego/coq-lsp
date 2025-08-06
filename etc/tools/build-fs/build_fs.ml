let readdir ~dir =
  Sys.readdir dir |> Array.map Filename.(concat dir) |> Array.to_list

let test_dir f = if Sys.is_directory f then Either.Left f else Right f

let filter_dir ~dir ~f entries =
  let sd, files = List.partition_map (fun d -> test_dir (Filename.concat dir d)) entries in
  let files = List.filter f files in
  sd, files

let scan_dir ~f ~dir =
  let rec aux dir prefix =
    let subdirs, files = Sys.readdir dir |> Array.to_list |> filter_dir ~dir ~f in
    files @ List.concat_map (fun sd -> aux sd (Filename.basename sd :: prefix)) subdirs
  in
  aux dir []

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
  let relative base dirs = List.fold_left (fun path dir -> Filename.concat path dir) base dirs
  let exists = Sys.file_exists
  let mkdir d = Sys.mkdir d 0o755
  let pp = Format.pp_print_string
end

module Rocq_config = struct
  type t = {
    opam_root : Path.t
  ; rocq_root : Path.t
  }

  let make () =
    let opam_root = Path.make Sys.argv.(1) in
    let rocq_root = Path.make Sys.argv.(2) in
    { opam_root; rocq_root }

end

let error args = Format.kfprintf (fun fmt -> Format.fprintf fmt "@\n%!"; exit 1) Format.err_formatter args

module Entry = struct
  type t = { src : Path.t ; dst : Path.t }

  (* "safe" copy function *)
  let copy { src; dst } =
    if not (Path.exists src) then
      error "[Entry.copy] source file not found: %a" Path.pp src
    else
      if (Path.exists dst) then
        error "[Entry.copy] destination file exists: %a" Path.pp src
      else
        Format.eprintf "copy %a to %a@\n" Path.pp src Path.pp dst
end

(* output config:

 - /static/lib = ocamlpath

 - Standard Rocq layout

   /static/rocq/theories
   /static/rocq/user_contrib
 *)

(* List of META files we need to copy, TODO: compute this list using ocamlfind *)
let meta_libs =
  [ "str"; "seq"; "uri"; "base"; "unix"; "zarith"; "yojson"; "findlib"; "dynlink";
                  "parsexp"; "sexplib"; "sexplib0"; "bigarray"; "cmdliner"; "ppx_hash"; "angstrom"; "stringext"; "ppx_compare"; "ppx_deriving"; "ppx_sexp_conv"; "memprof-limits"; "ppx_deriving_yojson" ]

(* Already linked libraries *)
let find_meta ~config:{ Rocq_config.opam_root; _ } ~dir =
  let meta_entry lib =
    let src = Path.relative opam_root [lib; "META"] in
    let dst = Path.relative dir ["static"; "lib"; lib; "META" ] in
    { Entry.src; dst} in
  List.map meta_entry meta_libs

let is_cma f = Filename.check_suffix f ".cma"

let make_cma src = { Entry.src; Entry.dst = src }

let find_plugins ~config:{ Rocq_config.rocq_root; _ } ~dir =
  (* Rocq path *)
  let rp = Path.relative rocq_root ["plugins"] in
  (* Serlib path *)
  let serlib_root = "_build/install/default/lib/coq-lsp/" in
  let sp = Path.relative serlib_root ["serlib"] in
  let pdirs_rocq = readdir ~dir:rp in
  (* Always local plugins *)
  let pdirs_serlib = readdir ~dir:sp in
  (* TODO Waterproof *)
  let pdirs = pdirs_rocq @ pdirs_serlib in
  (* Filter plugin dirs *)
  let pdirs = List.filter Sys.is_directory pdirs in
  let meta_entries =
    let rm =
      let src = Path.relative rocq_root ["META"] in
      let dst = Path.relative dir ["static"; "lib"; "rocq-runtime"; "META" ] in
      { Entry.src; dst} in
    let sm =
      let src = Path.relative serlib_root ["META"] in
      let dst = Path.relative dir ["static"; "lib"; "coq-lsp"; "META" ] in
      { Entry.src; dst} in
    [rm ; sm]
  in
  let cma_entries pdir =
    (* We could also just parse the META file *)
    let cmas = scan_dir ~f:is_cma ~dir:pdir in
    List.map make_cma cmas
  in
  meta_entries @ List.concat_map cma_entries pdirs

let find_vo ~config:_ ~dir:_ = []

(*
$$(find _build/install/default/lib/coq-lsp/  \( -wholename '*/serlib/*/*.js'  -or -wholename '*/META' \) -printf "%p:/static/lib/coq-lsp/%P ") \
$$(find $(_CCROOT)/../coq-waterproof/  \( -wholename '*/plugin/*.js'  -or -wholename '*/META' \) -printf "%p:/static/lib/coq-waterproof/%P ") \

   "find theories user-contrib
      \\( -wholename 'theories/*.vo' -or -wholename 'theories/*.glob' -or -wholename 'theories/*.v' -or -wholename 'user-contrib/*.vo' -or -wholename 'user-contrib/*.v' -or -wholename 'user-contrib/*.glob' \\) -printf \"$COQW/%p:/static/coqlib/%p \")")))

*)


let check_output_dir ~dir =
  if Path.exists dir then
    error "Output directory %a already exists" Path.pp dir

let build ~dir (files : Entry.t list) =
  check_output_dir ~dir;
  Path.mkdir dir;
  List.iter Entry.copy files

let compress ~dir:_ = ()

let main () =
  let dir = Path.make Sys.argv.(3) in
  let config = Rocq_config.make () in
  let meta_files = find_meta ~config ~dir in
  let plugins = find_plugins ~config ~dir in
  let vo = find_vo ~config ~dir in
  let all_files = meta_files @ plugins @ vo in
  build ~dir all_files;
  compress ~dir;
  ()

let () =
  Printexc.record_backtrace true;
  if Array.length Sys.argv < 4 then
    error "Error: not enough args. Format is:@\n build_fs opam_root rocq_root output_dir"
  else
    main ()
