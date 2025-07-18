(*************************************************************************)
(* Copyright 2015-2019 MINES ParisTech -- Dual License LGPL 2.1+ / GPL3+ *)
(* Copyright 2019-2024 Inria           -- Dual License LGPL 2.1+ / GPL3+ *)
(* Copyright 2024-2025 Emilio J. Gallego Arias  -- LGPL 2.1+ / GPL3+     *)
(* Copyright 2025      CNRS                     -- LGPL 2.1+ / GPL3+     *)
(* Written by: Emilio J. Gallego Arias & coq-lsp contributors            *)
(*************************************************************************)
(* Rocq Language Server Protocol: Rocq AST API                           *)
(*************************************************************************)

type t = Vernacexpr.vernac_control

let hash x = Serlib.Ser_vernacexpr.hash_vernac_control x
let compare x y = Serlib.Ser_vernacexpr.compare_vernac_control x y
let to_coq x = x
let of_coq x = x
let loc { CAst.loc; _ } = loc

(* Printer is very fiddly w.r.t. state, especially when used for debug, so we
   just let it fail for now. *)
let print x =
  try Ppvernac.pr_vernac x with _ -> Pp.str "XXX Coq printer crashed"

module Id = struct
  type t = Names.Id.t

  let of_string = Names.Id.of_string
  let of_coq x = x
  let to_coq x = x

  module Set = Names.Id.Set
  module Map = Names.Id.Map
end

module Qed = struct

  open Ppx_hash_lib.Std.Hash.Builtin
  open Ppx_compare_lib.Builtin
  module Loc = Serlib.Ser_loc
  module Attributes = Serlib.Ser_attributes
  module Vernacexpr = Serlib.Ser_vernacexpr

  type ast = t

  type t =
    { proof_end : Vernacexpr.proof_end
    ; loc : Loc.t option
    ; attrs : Attributes.vernac_flag list
    ; control : Vernacexpr.control_flag list
    }
  [@@deriving hash, compare]

  let extract = function
    | { CAst.v =
          { Vernacexpr.expr =
              Vernacexpr.(VernacSynPure (VernacEndProof proof_end))
          ; control
          ; attrs
          }
      ; loc
      } -> Some { proof_end; loc; attrs; control }
    | _ -> None
end

module Require = struct
  type ast = t

  open Ppx_hash_lib.Std.Hash.Builtin
  open Ppx_compare_lib.Builtin
  module Loc = Serlib.Ser_loc
  module Libnames = Serlib.Ser_libnames
  module Attributes = Serlib.Ser_attributes
  module Vernacexpr = Serlib.Ser_vernacexpr

  type t =
    { from : Libnames.qualid option
    ; export : Vernacexpr.export_with_cats option
    ; mods : (Libnames.qualid * Vernacexpr.import_filter_expr) list
    ; loc : Loc.t option
          [@ignore]
          [@hash.ignore]
          (* We need to ignore the loc of the Require statement, maybe it'd be
             better to keep the wrapping of the original vernac into a
             CAst.t? *)
    ; attrs : Attributes.vernac_flag list
    ; control : Vernacexpr.control_flag list
    }
  [@@deriving hash, compare]

  (** Determine if the Ast is a Require *)
  let extract = function
    | { CAst.v =
          { Vernacexpr.expr =
              Vernacexpr.(VernacSynterp (VernacRequire (from, export, mods)))
          ; control
          ; attrs
          }
      ; loc
      } -> Some { from; export; mods; loc; attrs; control }
    | _ -> None
end

module Meta = struct
  type ast = t

  open Ppx_hash_lib.Std.Hash.Builtin
  open Ppx_compare_lib.Builtin
  module Loc = Serlib.Ser_loc
  module Names = Serlib.Ser_names
  module Attributes = Serlib.Ser_attributes
  module Vernacexpr = Serlib.Ser_vernacexpr

  module Command = struct
    type t =
      | AbortAll
      | Back of int
      | ResetInitial
      | ResetName of Names.lident
      | Restart
    (* Not supported, but actually easy if we want | VernacUndo _ | VernacUndoTo
       _ *)
    [@@deriving hash, compare]
  end

  type t =
    { command : Command.t
    ; loc : Loc.t option
    ; attrs : Attributes.vernac_flag list
    ; control : Vernacexpr.control_flag list
    }
  [@@deriving hash, compare]

  (* EJGA: Coq classification puts these commands as pure? Seems like yet
     another bug... *)
  let extract : ast -> t option =
    CAst.with_loc_val (fun ?loc -> function
      | { Vernacexpr.expr = Vernacexpr.(VernacSynPure (VernacResetName id))
        ; control
        ; attrs
        } ->
        let command = Command.ResetName id in
        Some { command; loc; attrs; control }
      | { expr = VernacSynPure VernacResetInitial; control; attrs } ->
        let command = Command.ResetInitial in
        Some { command; loc; attrs; control }
      | { expr = VernacSynPure VernacRestart; control; attrs } ->
        let command = Command.Restart in
        Some { command; loc; attrs; control }
      | { expr = VernacSynPure (VernacBack num); control; attrs } ->
        let command = Command.Back num in
        Some { command; loc; attrs; control }
      | { expr = VernacSynPure VernacAbortAll; control; attrs } ->
        let command = Command.AbortAll in
        Some { command; loc; attrs; control }
      | _ -> None)
end

module Kinds = struct
  (* LSP kinds *)
  let _file = 1
  let _module_ = 2
  let _namespace = 3
  let _package = 4
  let class_ = 5
  let method_ = 6
  let _property = 7
  let field = 8
  let _constructor = 9
  let enum = 10
  let _interface = 11
  let function_ = 12
  let variable = 13
  let constant = 14
  let _string = 15
  let _number = 16
  let _boolean = 17
  let _array = 18
  let _object = 19
  let _key = 20
  let _null = 21
  let enumMember = 22
  let struct_ = 23
  let _event = 24
  let _operator = 25
  let _typeParameter = 26
end

let marshal_in ic : t = Marshal.from_channel ic
let marshal_out oc v = Marshal.to_channel oc v []

let pp_loc ?(print_file = false) fmt loc =
  let open Loc in
  let file =
    if print_file then
      match loc.fname with
      | ToplevelInput -> "Toplevel input: "
      | InFile { file; _ } -> "File \"" ^ file ^ "\": "
    else ""
  in
  Format.fprintf fmt "%sline: %d, col: %d -- line: %d, col: %d / {%d-%d}" file
    (loc.line_nb - 1) (loc.bp - loc.bol_pos) (loc.line_nb_last - 1)
    (loc.ep - loc.bol_pos_last)
    loc.bp loc.ep

let loc_to_string ?print_file loc =
  Format.asprintf "%a" (pp_loc ?print_file) loc

open CAst
open Vernacexpr

let inductive_detail = function
  | Inductive_kw -> (Kinds.enum, "Inductive")
  | CoInductive -> (Kinds.enum, "CoInductive")
  | Variant -> (Kinds.struct_, "Variant")
  | Record -> (Kinds.struct_, "Record")
  | Structure -> (Kinds.struct_, "Structure")
  | Class _ -> (Kinds.class_, "Class")

let assumption_detail = function
  | Decls.Definitional -> "Variable"
  | Logical -> "Axiom"
  | Conjectural -> "Parameter"
  | Context -> "Context"

let definition_detail = function
  | Decls.Definition -> "Definition"
  | Coercion -> "Coercion"
  | SubClass -> "SubClass"
  | CanonicalStructure -> "CanonicalStructure"
  | Example -> "Example"
  | Fixpoint -> "Fixpoint"
  | CoFixpoint -> "CoFixpoint"
  | Scheme -> "Scheme"
  | StructureComponent -> "StructureComponent"
  | IdentityCoercion -> "IdentityCoercion"
  | Instance -> "Instance"
  | Method -> "Method"
  | Let -> "Let"
  | LetContext -> "LetContext"

let theorem_detail = function
  | Decls.Theorem -> "Theorem"
  | Lemma -> "Lemma"
  | Fact -> "Fact"
  | Remark -> "Remark"
  | Property -> "Property"
  | Proposition -> "Proposition"
  | Corollary -> "Corollary"

let name_to_string = function
  | Names.Anonymous -> None
  | Names.Name id -> Some (Names.Id.to_string id)

let mk_name ~lines (id : Names.lname) : Lang.Ast.Name.t Lang.With_range.t =
  CAst.with_loc_val
    (fun ?loc id ->
      let loc = Option.get loc in
      let range = Utils.to_range ~lines loc in
      let v = name_to_string id in
      Lang.With_range.{ range; v })
    id

let mk_id ~lines (id : Names.lident) =
  CAst.map (fun id -> Names.Name id) id |> mk_name ~lines

let constructor_info ~lines ((_, (id, _typ)) : constructor_expr) =
  let range = Option.get id.loc in
  let range = Utils.to_range ~lines range in
  let name = mk_id ~lines id in
  let detail = "Constructor" in
  let kind = Kinds.enumMember in
  Lang.Ast.Info.make ~range ~name ~detail ~kind ()

let local_decl_expr_info ~lines ~kind ~detail (l : local_decl_expr) =
  let name =
    match l with
    | AssumExpr (ln, _, _) -> mk_name ~lines ln
    | DefExpr (ln, _, _, _) -> mk_name ~lines ln
  in
  let range = name.range in
  Lang.Ast.Info.make ~range ~name ~kind ~detail ()

let projection_info ~lines
    ((ld, _) : local_decl_expr * record_field_attr_unparsed) =
  let kind = Kinds.field in
  let detail = "Field" in
  local_decl_expr_info ~lines ~detail ~kind ld

let inductive_info ~lines ~range ikind (expr, _) =
  let (_, (id, _)), _, _, cons = expr in
  let name = mk_id ~lines id in
  match cons with
  | Constructors ci ->
    let children = List.map (constructor_info ~lines) ci in
    let kind, detail = inductive_detail ikind in
    Lang.Ast.Info.make ~range ~name ~kind ~detail ~children ()
  | RecordDecl (_, pi, _) ->
    let children = List.map (projection_info ~lines) pi in
    let kind, detail = inductive_detail ikind in
    Lang.Ast.Info.make ~range ~name ~kind ~detail ~children ()

let inductives_info ~lines ~range ikind idecls =
  match idecls with
  | [] -> None
  | inds -> Some (List.map (inductive_info ~lines ~range ikind) inds)

let ident_decl_info ~lines ~kind ~detail (lident, _) =
  let range = Option.get lident.loc in
  let range = Utils.to_range ~lines range in
  let name = mk_id ~lines lident in
  Lang.Ast.Info.make ~range ~name ~detail ~kind ()

let assumption_info ~lines kind (_, (ids, _)) =
  let detail = assumption_detail kind in
  let kind = Kinds.variable in
  List.map (ident_decl_info ~lines ~kind ~detail) ids

let fixpoint_info ~lines ~range { fname; _ } =
  let name = mk_id ~lines fname in
  let detail = "Fixpoint" in
  Lang.Ast.Info.make ~range ~name ~detail ~kind:Kinds.function_ ()

let symbol_info ~lines ~range
    ((_, (idents, _typs)) :
      (Constrexpr.ident_decl list * Constrexpr.constr_expr) with_coercion) =
  let detail = "Rewrite Symbol" in
  let mk_info (id, _) =
    let name = mk_id ~lines id in
    Lang.Ast.Info.make ~range ~name ~detail ~kind:Kinds.constant ()
  in
  List.map mk_info idents

let make_info ~st:_ ~lines CAst.{ loc; v } : Lang.Ast.Info.t list option =
  let open Vernacexpr in
  match loc with
  | None -> None
  | Some range -> (
    let range = Utils.to_range ~lines range in
    (* TODO: sections *)
    match v.expr with
    | VernacSynPure (VernacDefinition ((_, kind), (name, _), _)) ->
      let name = mk_name ~lines name in
      let detail = definition_detail kind in
      let kind = Kinds.function_ in
      Some [ Lang.Ast.Info.make ~range ~name ~detail ~kind () ]
    | VernacSynPure (VernacStartTheoremProof (kind, ndecls)) -> (
      let detail = theorem_detail kind in
      let kind = Kinds.function_ in
      match ndecls with
      | ((id, _), _) :: _ ->
        let name = mk_id ~lines id in
        Some [ Lang.Ast.Info.make ~range ~name ~detail ~kind () ]
      | [] -> None)
    | VernacSynPure (VernacInductive (ikind, idecls)) ->
      inductives_info ~lines ~range ikind idecls
    | VernacSynPure (VernacAssumption ((_, kind), _, ids)) ->
      Some (List.concat_map (assumption_info ~lines kind) ids)
    | VernacSynPure (VernacFixpoint (_, (_rec_expr, f_expr))) ->
      Some (List.map (fixpoint_info ~lines ~range) f_expr)
    | VernacSynPure (VernacInstance ((name, _), _, _, _, _)) ->
      let name = mk_name ~lines name in
      let kind = Kinds.method_ in
      let detail = "Instance" in
      Some [ Lang.Ast.Info.make ~range ~name ~kind ~detail () ]
    | VernacSynPure (VernacSymbol slist) ->
      Some (List.concat_map (symbol_info ~lines ~range) slist)
    | VernacSynPure (VernacAddRewRule (name, _)) ->
      let name = mk_id ~lines name in
      let kind = Kinds.method_ in
      let detail = "Rewrite Rule" in
      Some [ Lang.Ast.Info.make ~range ~name ~kind ~detail () ]
    | _ -> None)
