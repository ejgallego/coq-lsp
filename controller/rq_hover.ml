(************************************************************************)
(* Coq Language Server Protocol -- Requests                             *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2019-2023 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

open Lsp.Core

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

let info_of_id_at_point ~node id =
  let st = node.Fleche.Doc.Node.state in
  Coq.State.in_state ~st ~f:(info_of_id ~st) id

let pp_typ id = function
  | Def typ ->
    let typ = Pp.string_of_ppcmds typ in
    Format.(asprintf "```coq\n%s : %s\n```" id typ)
  | Notation nt ->
    let nt = Pp.string_of_ppcmds nt in
    Format.(asprintf "```coq\n%s\n```" nt)

let to_list x = Option.cata (fun x -> [ x ]) [] x

let info_type ~contents ~point ~node : string option =
  Option.bind (Rq_common.get_id_at_point ~contents ~point) (fun id ->
      match info_of_id_at_point ~node id with
      | Coq.Protect.{ E.r = R.Completed (Ok (Some info)); feedback = _ } ->
        Some (pp_typ id info)
      | _ -> None)

let extract_def ~point:_ (def : Vernacexpr.definition_expr) :
    Constrexpr.constr_expr list =
  match def with
  | Vernacexpr.ProveBody (_bl, et) -> [ et ]
  | Vernacexpr.DefineBody (_bl, _, et, eb) -> [ et ] @ to_list eb

let extract_pexpr ~point:_ (pexpr : Vernacexpr.proof_expr) :
    Constrexpr.constr_expr list =
  let _id, (_bl, et) = pexpr in
  [ et ]

let extract ~point ast =
  match (Coq.Ast.to_coq ast).v.expr with
  | Vernacexpr.(VernacSynPure (VernacDefinition (_, _, expr))) ->
    extract_def ~point expr
  | Vernacexpr.(VernacSynPure (VernacStartTheoremProof (_, pexpr))) ->
    List.concat_map (extract_pexpr ~point) pexpr
  | _ -> []

let ntn_key_info (_entry, key) = "notation: " ^ key

let info_notation ~point (ast : Fleche.Doc.Node.Ast.t) =
  (* XXX: Iterate over the results *)
  match extract ~point ast.v with
  | { CAst.v = Constrexpr.CNotation (_, key, _params); _ } :: _ ->
    Some (ntn_key_info key)
  | _ -> None

let info_notation ~contents:_ ~point ~node : string option =
  Option.bind node.Fleche.Doc.Node.ast (info_notation ~point)

open Fleche

(* Hover handler *)
module Handler = struct
  (** Returns [Some markdown] if there is some hover to match *)
  type 'node h_node =
    contents:Contents.t -> point:int * int -> node:'node -> string option

  type h_doc =
    doc:Doc.t -> point:int * int -> node:Doc.Node.t option -> string option

  type t =
    | MaybeNode : Doc.Node.t option h_node -> t
    | WithNode : Doc.Node.t h_node -> t
    | WithDoc : h_doc -> t
end

module type HoverProvider = sig
  val h : Handler.t
end

module Loc_info : HoverProvider = struct
  let h ~contents:_ ~point:_ ~node =
    match node with
    | None -> "no node here"
    | Some node ->
      let range = Doc.Node.range node in
      Format.asprintf "%a" Lang.Range.pp range

  let h ~contents ~point ~node =
    if !Config.v.show_loc_info_on_hover then Some (h ~contents ~point ~node)
    else None

  let h = Handler.MaybeNode h
end

module Stats : HoverProvider = struct
  let h ~contents:_ ~point:_ ~node =
    if !Config.v.show_stats_on_hover then Some Doc.Node.(Info.print (info node))
    else None

  let h = Handler.WithNode h
end

module Type : HoverProvider = struct
  let h = Handler.WithNode info_type
end

module Notation : HoverProvider = struct
  let h = Handler.WithNode info_notation
end

module Register = struct
  let handlers : Handler.t list ref = ref []
  let add fn = handlers := fn :: !handlers

  let handle ~(doc : Doc.t) ~point ~node =
    let contents = doc.contents in
    function
    | Handler.MaybeNode h -> h ~contents ~point ~node
    | Handler.WithNode h ->
      Option.bind node (fun node -> h ~contents ~point ~node)
    | Handler.WithDoc h -> h ~doc ~point ~node

  let fire ~doc ~point ~node =
    List.filter_map (handle ~doc ~point ~node) !handlers
end

(* Register in-file hover plugins *)
let () = List.iter Register.add [ Loc_info.h; Stats.h; Type.h; Notation.h ]

let hover ~doc ~point =
  let node = Info.LC.node ~doc ~point Exact in
  let range = Option.map Doc.Node.range node in
  let hovers = Register.fire ~doc ~point ~node in
  match hovers with
  | [] -> `Null
  | hovers ->
    let value = String.concat "\n___\n" hovers in
    let contents = { HoverContents.kind = "markdown"; value } in
    HoverInfo.(to_yojson { contents; range })

let hover ~doc ~point = hover ~doc ~point |> Result.ok
