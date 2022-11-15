module Vernacexpr = Serlib.Ser_vernacexpr

type t = Vernacexpr.vernac_control

let hash x = Serlib.Ser_vernacexpr.hash_vernac_control x
let compare x y = Serlib.Ser_vernacexpr.compare_vernac_control x y
let loc { CAst.loc; _ } = loc

(* Printer is very fiddly w.r.t. state, especially when used for debug, so we
   just let it fail for now. *)
let print x =
  try Ppvernac.pr_vernac x with _ -> Pp.str "XXX Coq printer crashed"

let match_coq_def f v : _ list =
  let open Vernacexpr in
  let ndecls =
    (* TODO: (co)fixpoint, instance, assumption *)
    match v.CAst.v.expr with
    | VernacDefinition (_, (CAst.{ loc = Some loc; v = name }, _), _) ->
      Nameops.Name.fold_left (fun _ id -> [ (loc, id) ]) [] name
    | VernacStartTheoremProof (_, ndecls) ->
      let f_id = function
        | (CAst.{ loc = None; _ }, _), _ -> None
        | (CAst.{ loc = Some loc; v }, _), _ -> Some (loc, v)
      in
      CList.map_filter f_id ndecls
    | _ -> []
  in
  CList.map (fun (loc, id) -> f loc id) ndecls

(* | VernacLoad (_, _) -> (??) | VernacSyntaxExtension (_, _) -> (??) |
   VernacOpenCloseScope (_, _) -> (??) | VernacDeclareScope _ -> (??) |
   VernacDelimiters (_, _) -> (??) | VernacBindScope (_, _) -> (??) |
   VernacInfix (_, _, _) -> (??) | VernacNotation (_, _, _) -> (??) |
   VernacNotationAddFormat (_, _, _) -> (??) | VernacDeclareCustomEntry _ ->
   (??) | VernacEndProof _ -> (??) | VernacExactProof _ -> (??) |
   VernacAssumption (_, _, _) -> (??) | VernacInductive (_, _, _, _) -> (??) |
   VernacFixpoint (_, _) -> (??) | VernacCoFixpoint (_, _) -> (??) |
   VernacScheme _ -> (??) | VernacCombinedScheme (_, _) -> (??) | VernacUniverse
   _ -> (??) | VernacConstraint _ -> (??) | VernacBeginSection _ -> (??) |
   VernacEndSegment _ -> (??) | VernacRequire (_, _, _) -> (??) | VernacImport
   (_, _) -> (??) | VernacCanonical _ -> (??) | VernacCoercion (_, _, _) -> (??)
   | VernacIdentityCoercion (_, _, _) -> (??) | VernacNameSectionHypSet (_, _)
   -> (??) | VernacInstance (_, _, _, _) -> (??) | VernacDeclareInstance (_, _,
   _) -> (??) | VernacContext _ -> (??) | VernacExistingInstance _ -> (??) |
   VernacExistingClass _ -> (??) | VernacDeclareModule (_, _, _, _) -> (??) |
   VernacDefineModule (_, _, _, _, _) -> (??) | VernacDeclareModuleType (_, _,
   _, _) -> (??) | VernacInclude _ -> (??) | VernacSolveExistential (_, _) ->
   (??) | VernacAddLoadPath (_, _, _) -> (??) | VernacRemoveLoadPath _ -> (??) |
   VernacAddMLPath (_, _) -> (??) | VernacDeclareMLModule _ -> (??) |
   VernacChdir _ -> (??) | VernacWriteState _ -> (??) | VernacRestoreState _ ->
   (??) | VernacResetName _ -> (??) | VernacResetInitial -> (??) | VernacBack _
   -> (??) | VernacBackTo _ -> (??) | VernacCreateHintDb (_, _) -> (??) |
   VernacRemoveHints (_, _) -> (??) | VernacHints (_, _) -> (??) |
   VernacSyntacticDefinition (_, _, _) -> (??) | VernacArguments (_, _, _, _, _)
   -> (??) | VernacReserve _ -> (??) | VernacGeneralizable _ -> (??) |
   VernacSetOpacity _ -> (??) | VernacSetStrategy _ -> (??) | VernacUnsetOption
   (_, _) -> (??) | VernacSetOption (_, _, _) -> (??) | VernacAddOption (_, _)
   -> (??) | VernacRemoveOption (_, _) -> (??) | VernacMemOption (_, _) -> (??)
   | VernacPrintOption _ -> (??) | VernacCheckMayEval (_, _, _) -> (??) |
   VernacGlobalCheck _ -> (??) | VernacDeclareReduction (_, _) -> (??) |
   VernacPrint _ -> (??) | VernacSearch (_, _, _) -> (??) | VernacLocate _ ->
   (??) | VernacRegister (_, _) -> (??) | VernacPrimitive (_, _, _) -> (??) |
   VernacComments _ -> (??) | VernacAbort _ -> (??) | VernacAbortAll -> (??) |
   VernacRestart -> (??) | VernacUndo _ -> (??) | VernacUndoTo _ -> (??) |
   VernacFocus _ -> (??) | VernacUnfocus -> (??) | VernacUnfocused -> (??) |
   VernacBullet _ -> (??) | VernacSubproof _ -> (??) | VernacEndSubproof -> (??)
   | VernacShow _ -> (??) | VernacCheckGuard -> (??) | VernacProof (_, _) ->
   (??) | VernacProofMode _ -> (??) | VernacExtend (_, _) -> (??)) *)

let grab_definitions f nodes =
  List.fold_left (fun acc s -> match_coq_def f s @ acc) [] nodes

let marshal_in ic : t = Marshal.from_channel ic
let marshal_out oc v = Marshal.to_channel oc v []

module Internal = struct
  let to_coq x = x
  let of_coq x = x
end

(* Structure inference *)
module View = struct
  type ast = t

  type t =
    (* This could be also extracted from the interpretation *)
    | Open of unit
    | End of unit
    | Require of
        { prefix : Libnames.qualid option
        ; refs : Libnames.qualid list
        }
    | Other

  let kind ast =
    match ast.CAst.v.Vernacexpr.expr with
    | Vernacexpr.VernacStartTheoremProof _ -> Open ()
    | Vernacexpr.VernacEndProof _ -> End ()
    | Vernacexpr.VernacRequire (prefix, _export, module_refs) ->
      let refs = List.map fst module_refs in
      Require { prefix; refs }
    | _ -> Other
end

module Id = Names.Id

module QualId = struct
  type t = Libnames.qualid
end
