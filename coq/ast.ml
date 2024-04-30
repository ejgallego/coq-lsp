(* module Vernacexpr = Serlib.Ser_vernacexpr *)

type t = Vernacexpr.vernac_control

(* let hash x = Serlib.Ser_vernacexpr.hash_vernac_control x *)
(* let compare x y = Serlib.Ser_vernacexpr.compare_vernac_control x y *)

let hash x = Hashtbl.hash x
let compare x y = Stdlib.compare x y
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
  let _constant = 14
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
      | InFile file -> "File \"" ^ file ^ "\": "
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

let ud = ref (fun x -> x)

let mk_name ~lines (id : Names.lname) : Lang.Ast.Name.t Lang.With_range.t =
  CAst.with_loc_val
    (fun ?loc id ->
      let loc = Option.get loc in
      let range = Utils.to_range ~lines (!ud loc) in
      let v = name_to_string id in
      Lang.With_range.{ range; v })
    id

let mk_id ~lines (id : Names.lident) =
  CAst.map (fun id -> Names.Name id) id |> mk_name ~lines

let constructor_info ~lines ((_, (id, _typ)) : constructor_expr) =
  let range = Option.get id.loc in
  let range = Utils.to_range ~lines (!ud range) in
  let name = mk_id ~lines id in
  let detail = "Constructor" in
  let kind = Kinds.enumMember in
  Lang.Ast.Info.make ~range ~name ~detail ~kind ()

let local_decl_expr_info ~lines ~kind ~detail (l : local_decl_expr) =
  let name =
    match l with
    | AssumExpr (ln, _) -> mk_name ~lines ln
    | DefExpr (ln, _, _) -> mk_name ~lines ln
  in
  let range = name.range in
  Lang.Ast.Info.make ~range ~name ~kind ~detail ()

let projection_info ~lines ((ld, _) : local_decl_expr * record_field_attr) =
  let kind = Kinds.field in
  let detail = "Field" in
  local_decl_expr_info ~lines ~detail ~kind ld



  (* ident_decl with_coercion * local_binder_expr list * constr_expr option * inductive_kind * *)
  (*   constructor_list_or_record_decl_expr *)

let inductive_info ~lines ~range ((expr : Vernacexpr.inductive_expr), _) =
  let ((_, (id, _)), _, _, ikind, cons) = expr in
  let name = mk_id ~lines id in
  match cons with
  | Constructors ci ->
    let children = List.map (constructor_info ~lines) ci in
    let kind, detail = inductive_detail ikind in
    Lang.Ast.Info.make ~range ~name ~kind ~detail ~children ()
  | RecordDecl (_, pi) ->
    let children = List.map (projection_info ~lines) pi in
    let kind, detail = inductive_detail ikind in
    Lang.Ast.Info.make ~range ~name ~kind ~detail ~children ()

let inductives_info ~lines ~range idecls =
  match idecls with
  | [] -> None
  | inds -> Some (List.map (inductive_info ~lines ~range) inds)

let ident_decl_info ~lines ~kind ~detail (lident, _) =
  let range = Option.get lident.loc in
  let range = Utils.to_range ~lines (!ud range) in
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

let make_info ~st:_ ~lines CAst.{ loc; v } : Lang.Ast.Info.t list option =
  let open Vernacexpr in
  match loc with
  | None -> None
  | Some range -> (
    let range = Utils.to_range ~lines range in
    (* TODO: sections *)
    match v.expr with
    | VernacDefinition ((_, kind), (name, _), _) ->
      let name = mk_name ~lines name in
      let detail = definition_detail kind in
      let kind = Kinds.function_ in
      Some [ Lang.Ast.Info.make ~range ~name ~detail ~kind () ]
    | VernacStartTheoremProof (kind, ndecls) -> (
      let detail = theorem_detail kind in
      let kind = Kinds.function_ in
      match ndecls with
      | ((id, _), _) :: _ ->
        let name = mk_id ~lines id in
        Some [ Lang.Ast.Info.make ~range ~name ~detail ~kind () ]
      | [] -> None)
    | VernacInductive (_, _, _, idecls) ->
      inductives_info ~lines ~range idecls
    | VernacAssumption ((_, kind), _, ids) ->
      Some (List.concat_map (assumption_info ~lines kind) ids)
    | VernacFixpoint (_, f_expr) ->
      Some (List.map (fixpoint_info ~lines ~range) f_expr)
    | VernacInstance ((name, _), _, _, _, _) ->
      let name = mk_name ~lines name in
      let kind = Kinds.method_ in
      let detail = "Instance" in
      Some [ Lang.Ast.Info.make ~range ~name ~kind ~detail () ]
    | _ -> None)
