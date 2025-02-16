(************************************************************************)
(* Coq Language Server Protocol -- Requests                             *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2019-2024 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

open Fleche_lsp.Core

(* Taken from printmod.ml, funny stuff! *)
let build_ind_type mip = Inductive.type_of_inductive mip

type id_info =
  | Notation of Pp.t
  | Def of
      { typ : Pp.t  (** type of the ide *)
      ; params : Pp.t  (** params that need display next to the name *)
      ; full_path : Pp.t option
            (** full path of the constant, if any, for example
                [Stdlib.Lists.map] *)
      ; source : string option  (** filename where the constant is located *)
      }

let print_params env sigma params =
  if CList.is_empty params then Pp.mt ()
  else Pp.(spc () ++ Printer.pr_rel_context env sigma params ++ brk (1, 2))

let info_of_ind env ((sp, i) : Names.Ind.t) =
  let udecl = None in
  let mib = Environ.lookup_mind sp env in
  let bl =
    Printer.universe_binders_with_opt_names
      (Declareops.inductive_polymorphic_context mib)
      udecl
  in
  let sigma = Evd.from_ctx (UState.of_names bl) in
  let u =
    UVars.make_abstract_instance (Declareops.inductive_polymorphic_context mib)
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
  let inst =
    if Declareops.inductive_is_polymorphic mib then
      Printer.pr_universe_instance sigma u
    else Pp.mt ()
  in
  let params = EConstr.Unsafe.to_rel_context params in
  let typ = Printer.pr_ltype_env ~impargs env_params sigma arity in
  let params = Pp.(inst ++ print_params env sigma params) in
  let full_path = Some (Names.MutInd.print sp) in
  let source =
    let dp = Names.MutInd.modpath sp |> Names.ModPath.dp in
    Coq.Module.(make dp |> Result.to_option |> Option.map source)
  in
  Def { typ; params; full_path; source }

let type_of_constant cb = cb.Declarations.const_type

let info_of_const env cr =
  let udecl = None in
  let cdef = Environ.lookup_constant cr env in
  let bl =
    Printer.universe_binders_with_opt_names
      (Environ.constant_context env cr)
      udecl
  in
  let sigma = Evd.from_ctx (UState.of_names bl) in
  (* This prints the definition *)
  (* let cb = Environ.lookup_constant cr env in *)
  (* Option.cata (fun (cb,_univs,_uctx) -> Some cb ) None *)
  (*   (Global.body_of_constant_body Library.indirect_accessor cb), *)
  let typ = type_of_constant cdef in
  let univs = Declareops.constant_polymorphic_context cdef in
  let inst = UVars.make_abstract_instance univs in
  let impargs =
    Impargs.select_stronger_impargs
      (Impargs.implicits_of_global (Names.GlobRef.ConstRef cr))
  in
  let impargs = List.map Impargs.binding_kind_of_status impargs in
  let typ = Printer.pr_ltype_env env sigma ~impargs typ in
  let inst =
    if Environ.polymorphic_constant cr env then
      Printer.pr_universe_instance sigma inst
    else Pp.mt ()
  in
  let full_path = Some (Names.Constant.print cr) in
  let source =
    let dp = Names.Constant.modpath cr |> Names.ModPath.dp in
    Coq.Module.(make dp |> Result.to_option |> Option.map source)
  in
  Def { typ; params = inst; full_path; source }

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

let print_type env sigma x =
  Def
    { typ = Printer.pr_ltype_env env sigma x
    ; params = Pp.mt ()
    ; full_path = None
    ; source = None
    }

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
        | ConstRef cr -> info_of_const env cr
        | IndRef ir -> info_of_ind env ir
        | ConstructRef cr -> info_of_constructor env cr |> print_type env sigma)
        |> fun x -> Some x
      | Abbrev kn ->
        Some
          (Notation
             (Prettyp.print_abbreviation
                (Library.indirect_accessor [@warning "-3"]) env sigma kn))
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
  Coq.State.in_state ~token ~st ~f:(info_of_id ~st) id

let pp_cr fmt = function
  | None -> ()
  | Some cr -> Format.fprintf fmt " - **full path**: `%a`@\n" Pp.pp_with cr

let pp_file fmt = function
  | None -> ()
  | Some file -> Format.fprintf fmt " - **in file**: `%s`" file

let pp_typ id = function
  | Def { typ; params; full_path; source } ->
    let typ = Pp.string_of_ppcmds typ in
    let param = Pp.string_of_ppcmds params in
    Format.(
      asprintf "@[```coq\n%s%s: %s@\n```@\n@[%a@]@[%a@]@]" id param typ pp_cr
        full_path pp_file source)
  | Notation nt ->
    let nt = Pp.string_of_ppcmds nt in
    Format.(asprintf "```coq\n%s\n```" nt)

let to_list x = Option.cata (fun x -> [ x ]) [] x

let info_type ~token ~contents ~point ~node : string option =
  Option.bind (Rq_common.get_id_at_point ~contents ~point) (fun id ->
      match info_of_id_at_point ~token ~node id with
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

(* Disabled until it is more useful and doesn't pre-empt other stuff. *)
let info_notation ~token:_ ~contents:_ ~point ~node : string option =
  if false then Option.bind node.Fleche.Doc.Node.ast (info_notation ~point)
  else None

open Fleche

(* Hover handler *)
module Handler = struct
  (** Returns [Some markdown] if there is some hover to match *)
  type 'node h_node =
       token:Coq.Limits.Token.t
    -> contents:Contents.t
    -> point:int * int
    -> node:'node
    -> string option

  type h_doc =
       token:Coq.Limits.Token.t
    -> doc:Doc.t
    -> point:int * int
    -> node:Doc.Node.t option
    -> string option

  type t =
    | MaybeNode : Doc.Node.t option h_node -> t
    | WithNode : Doc.Node.t h_node -> t
    | WithDoc : h_doc -> t
end

module type HoverProvider = sig
  val h : Handler.t
end

module Loc_info : HoverProvider = struct
  let h ~token:_ ~contents:_ ~point:_ ~node =
    match node with
    | None -> "no node here"
    | Some node ->
      let range = Doc.Node.range node in
      Format.asprintf "%a" Lang.Range.pp range

  let h ~token ~contents ~point ~node =
    if !Config.v.show_loc_info_on_hover then
      Some (h ~token ~contents ~point ~node)
    else None

  let h = Handler.MaybeNode h
end

module Stats : HoverProvider = struct
  let h ~token:_ ~contents:_ ~point:_ ~node =
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

module InputHelp : HoverProvider = struct
  let mk_map map =
    List.fold_left
      (fun m (tex, uni) -> CString.Map.add uni tex m)
      CString.Map.empty map

  (* A bit hackish, but OK *)
  let unimap =
    Lazy.from_fun (fun () -> mk_map (Unicode_bindings.from_config ()))

  let input_help ~token:_ ~contents ~point ~node:_ =
    (* check if contents at point match *)
    match Rq_common.get_uchar_at_point ~prev:false ~contents ~point with
    | Some (uchar, uchar_str)
      when Lang.Compat.OCaml4_14.Uchar.utf_8_byte_length uchar > 1 ->
      Option.map
        (fun tex -> Format.asprintf "Input %s with %s" uchar_str tex)
        (CString.Map.find_opt uchar_str (Lazy.force unimap))
    | Some _ | None -> None

  let h = Handler.MaybeNode input_help
end

module UniDiff = struct
  let show_unidiff ~token ?diff ~st () =
    let nuniv_prev, nconst_prev =
      match diff with
      | Some st -> (
        match Coq.State.info_universes ~token ~st with
        | Coq.Protect.{ E.r = R.Completed (Ok (nuniv, nconst)); feedback = _ }
          -> (nuniv, nconst)
        | _ -> (0, 0))
      | None -> (0, 0)
    in
    match Coq.State.info_universes ~token ~st with
    | Coq.Protect.{ E.r = R.Completed (Ok (nuniv, nconst)); feedback = _ } ->
      Some
        (Format.asprintf "@[univ data (%4d,%4d) {+%d, +%d}@\n@]" nuniv nconst
           (nuniv - nuniv_prev) (nconst - nconst_prev))
    | _ -> None

  let h ~token ~contents:_ ~point:_ ~(node : Fleche.Doc.Node.t) =
    if !Fleche.Config.v.show_universes_on_hover then
      let diff = Option.map Fleche.Doc.Node.state node.prev in
      show_unidiff ~token ?diff ~st:node.state ()
    else None

  let h = Handler.WithNode h
end

module Register = struct
  let handlers : Handler.t list ref = ref []
  let add fn = handlers := fn :: !handlers

  let handle ~token ~(doc : Doc.t) ~point ~node =
    let contents = doc.contents in
    function
    | Handler.MaybeNode h -> h ~token ~contents ~point ~node
    | Handler.WithNode h ->
      Option.bind node (fun node -> h ~token ~contents ~point ~node)
    | Handler.WithDoc h -> h ~token ~doc ~point ~node

  let fire ~token ~doc ~point ~node =
    List.filter_map (handle ~token ~doc ~point ~node) !handlers
end

(* Register in-file hover plugins *)
let () =
  List.iter Register.add
    [ Loc_info.h; Stats.h; Type.h; Notation.h; InputHelp.h; UniDiff.h ]

let hover ~token ~(doc : Fleche.Doc.t) ~point =
  let node = Info.LC.node ~doc ~point Exact in
  let range = Option.map Doc.Node.range node in
  let hovers = Register.fire ~token ~doc ~point ~node in
  match hovers with
  | [] -> `Null
  | hovers ->
    let value = String.concat "\n___\n" hovers in
    let contents = { HoverContents.kind = "markdown"; value } in
    HoverInfo.(to_yojson { contents; range })

let hover ~token ~doc ~point = hover ~token ~doc ~point |> Result.ok
