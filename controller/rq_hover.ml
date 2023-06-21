(************************************************************************)
(* Coq Language Server Protocol -- Requests                             *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2019-2023 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

open Lsp.Core

(* Debug parameters *)
let show_loc_info = false

(* Taken from printmod.ml, funny stuff! *)
let build_ind_type mip = Inductive.type_of_inductive mip

type id_info =
  | Notation of Pp.t
  | Def of Pp.t

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
    Reduction.hnf_prod_applist_decls env nparamdecls
      (build_ind_type ((mib, mip), u))
      args
  in
  let impargs =
    Impargs.select_stronger_impargs
      (Impargs.implicits_of_global (Names.GlobRef.IndRef (sp, i)))
  in
  let impargs = List.map Impargs.binding_kind_of_status impargs in
  Def (Printer.pr_ltype_env ~impargs env_params sigma arity)

let type_of_constant cb = cb.Declarations.const_type

let info_of_const env sigma cr =
  let cdef = Environ.lookup_constant cr env in
  (* This prints the definition *)
  (* let cb = Environ.lookup_constant cr env in *)
  (* Option.cata (fun (cb,_univs,_uctx) -> Some cb ) None *)
  (*   (Global.body_of_constant_body Library.indirect_accessor cb), *)
  let typ = type_of_constant cdef in
  let impargs =
    Impargs.select_stronger_impargs
      (Impargs.implicits_of_global (Names.GlobRef.ConstRef cr))
  in
  let impargs = List.map Impargs.binding_kind_of_status impargs in
  Def (Printer.pr_ltype_env env sigma ~impargs typ)

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

let print_type env sigma x = Def (Printer.pr_ltype_env env sigma x)

let info_of_id env sigma id =
  let qid = Libnames.qualid_of_string id in
  try
    let id = Names.Id.of_string id in
    Some (info_of_var env id |> print_type env sigma)
  with _ -> (
    try
      (* try locate the kind of object the name refers to *)
      match Nametab.locate_extended qid with
      | TrueGlobal lid ->
        (* dispatch based on type *)
        let open Names.GlobRef in
        (match lid with
        | VarRef vr -> info_of_var env vr |> print_type env sigma
        | ConstRef cr -> info_of_const env sigma cr
        | IndRef ir -> info_of_ind env sigma ir
        | ConstructRef cr -> info_of_constructor env cr |> print_type env sigma)
        |> fun x -> Some x
      | Abbrev kn -> Some (Notation (Prettyp.print_abbreviation env kn))
    with _ -> None)

let info_of_id ~st id =
  let st = Coq.State.to_coq st in
  let sigma, env =
    match st with
    | { Vernacstate.interp = { lemmas = Some pstate; _ }; _ } ->
      Vernacstate.LemmaStack.with_top pstate
        ~f:Declare.Proof.get_current_context
    | _ ->
      let env = Global.env () in
      (Evd.from_env env, env)
  in
  info_of_id env sigma id

let info_of_id_at_point ~token ~node id =
  let st = node.Fleche.Doc.Node.state in
  Fleche.Info.LC.in_state ~token ~st ~f:(info_of_id ~st) id

let pp_typ id = function
  | Def typ ->
    let typ = Pp.string_of_ppcmds typ in
    Format.(asprintf "```coq\n%s : %s\n```" id typ)
  | Notation nt ->
    let nt = Pp.string_of_ppcmds nt in
    Format.(asprintf "```coq\n%s\n```" nt)

let if_bool b l = if b then [ l ] else []
let to_list = Option.cata (fun x -> [ x ]) []

let hover ~token ~doc ~node ~point =
  let open Fleche in
  let range = Doc.Node.range node in
  let info = Doc.Node.info node in
  let range_string = Format.asprintf "%a" Lang.Range.pp range in
  let stats_string = Doc.Node.Info.print info in
  let type_string =
    Option.bind (Rq_common.get_id_at_point ~doc ~point) (fun id ->
        Option.map (pp_typ id) (info_of_id_at_point ~token ~node id))
  in
  let hovers =
    if_bool show_loc_info range_string
    @ if_bool !Config.v.show_stats_on_hover stats_string
    @ to_list type_string
  in
  match hovers with
  | [] -> `Null
  | hovers ->
    let range = Some range in
    let value = String.concat "\n___\n" hovers in
    let contents = { HoverContents.kind = "markdown"; value } in
    HoverInfo.(to_yojson { contents; range })

let hover ~token ~doc ~point =
  let node = Fleche.Info.LC.node ~doc ~point Exact in
  (match node with
  | None ->
    if show_loc_info then
      let contents =
        { HoverContents.kind = "markdown"; value = "no node here" }
      in
      HoverInfo.(to_yojson { contents; range = None })
    else `Null
  | Some node -> hover ~token ~doc ~node ~point)
  |> Result.ok
