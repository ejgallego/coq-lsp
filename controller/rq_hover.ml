(************************************************************************)
(* Coq Language Server Protocol -- Requests                             *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2019-2023 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

open Lsp.JFleche

(* Debug parameters *)
let show_loc_info = false

(* Taken from printmod.ml, funny stuff! *)
let build_ind_type mip = Inductive.type_of_inductive mip

let info_of_ind env sigma ((sp, i) : Names.Ind.t) =
  let mib = Environ.lookup_mind sp env in
  let u =
    Univ.make_abstract_instance (Declareops.inductive_polymorphic_context mib)
  in
  let mip = mib.Declarations.mind_packets.(i) in
  let paramdecls = Inductive.inductive_paramdecls (mib, u) in
  let env_params, params =
    Namegen.make_all_rel_context_name_different env (Evd.from_env env)
      (EConstr.of_rel_context paramdecls)
  in
  let nparamdecls = Context.Rel.length params in
  let args = Context.Rel.instance_list Constr.mkRel 0 params in
  let arity =
    Reduction.hnf_prod_applist_assum env nparamdecls
      (build_ind_type ((mib, mip), u))
      args
  in
  Printer.pr_lconstr_env env_params sigma arity

let type_of_constant cb = cb.Declarations.const_type

let info_of_const env cr =
  let cdef = Environ.lookup_constant cr env in
  (* This prints the definition *)
  (* let cb = Environ.lookup_constant cr env in *)
  (* Option.cata (fun (cb,_univs,_uctx) -> Some cb ) None *)
  (*   (Global.body_of_constant_body Library.indirect_accessor cb), *)
  type_of_constant cdef

let info_of_var env vr =
  let vdef = Environ.lookup_named vr env in
  (* This prints the value if some *)
  (* Option.cata (fun cb -> Some cb) None (Context.Named.Declaration.get_value
     vdef) *)
  Context.Named.Declaration.get_type vdef

(* XXX: Some work to do wrt Global.type_of_global_unsafe *)
let info_of_constructor env cr =
  (* let cdef = Global.lookup_pinductive (cn, cu) in *)
  let ctype, _uctx =
    Typeops.type_of_global_in_context env (Names.GlobRef.ConstructRef cr)
  in
  ctype

let info_of_id env sigma id =
  let qid = Libnames.qualid_of_string id in
  (* try locate the kind of object the name refers to *)
  try
    let lid = Nametab.locate qid in
    (* dispatch based on type *)
    let open Names.GlobRef in
    (match lid with
    | VarRef vr -> info_of_var env vr |> Printer.pr_type_env env sigma
    | ConstRef cr -> info_of_const env cr |> Printer.pr_type_env env sigma
    | IndRef ir -> info_of_ind env sigma ir
    | ConstructRef cr ->
      info_of_constructor env cr |> Printer.pr_type_env env sigma)
    |> fun x -> Some x
  with _ -> (
    try
      let id = Names.Id.of_string id in
      Some (info_of_var env id |> Printer.pr_type_env env sigma)
    with _ -> None)

let info_of_id ~st id =
  let st = Coq.State.to_coq st in
  let sigma, env =
    match st with
    | { Vernacstate.lemmas = Some pstate; _ } ->
      Vernacstate.LemmaStack.with_top pstate
        ~f:Declare.Proof.get_current_context
    | _ ->
      let env = Global.env () in
      (Evd.from_env env, env)
  in
  info_of_id env sigma id

let info_of_id_at_point ~doc ~point id =
  let st = Fleche.Info.LC.node ~doc ~point Exact in
  Option.bind st (fun node ->
      let st = node.Fleche.Doc.Node.state in
      Fleche.Info.LC.in_state ~st ~f:(info_of_id ~st) id)

let hover ~doc ~point =
  let range_span = Fleche.Info.LC.range ~doc ~point Exact in
  let range_string =
    let none fmt () = Format.fprintf fmt "no ast" in
    Format.asprintf "%a" (Format.pp_print_option ~none Lang.Range.pp) range_span
  in
  let info_string =
    Fleche.Info.LC.info ~doc ~point Exact
    |> Option.map Fleche.Doc.Node.Info.print
    |> Option.default "no info"
  in
  let hover_string =
    if show_loc_info then range_string ^ "\n___\n" ^ info_string
    else info_string
  in
  let hover_string =
    match Rq_common.get_id_at_point ~doc ~point with
    | Some id -> (
      match info_of_id_at_point ~doc ~point id with
      | None -> hover_string
      | Some typ ->
        let typ = Pp.string_of_ppcmds typ in
        Format.asprintf "```coq\n%s : %s\n```\n___\n%s" id typ hover_string)
    | None -> hover_string
  in
  let contents = { HoverContents.kind = "markdown"; value = hover_string } in
  let range = range_span in
  HoverInfo.(to_yojson { contents; range })
