open Base
open Fleche
module F = Stdlib.Format

(* This is actually quite a weak check, just a placeholder as Flèche can tells
   us precisely what has opened a proof; but we need to bump the dep. *)
let check_thm (info : Lang.Ast.Info.t) =
  let ( = ) = Poly.equal in
  info.kind = 12
  && (info.detail = Some "Theorem"
     || info.detail = Some "Lemma"
     || info.detail = Some "Proposition"
     || info.detail = Some "Corollary"
     || info.detail = Some "Definition"
     || info.detail = Some "Fixpoint"
     || info.detail = Some "Fact")

let check_thm infos = List.exists ~f:check_thm infos

(* A node can have multiple names (ie mutual recursive defs) *)
let get_names (infos : Lang.Ast.Info.t list) =
  List.concat_map infos ~f:(fun (info : Lang.Ast.Info.t) ->
      match info.name.v with
      | None -> []
      | Some s -> [ s ])

module ThmDecl = struct
  type t =
    { names : string list
    ; node : Doc.Node.t
    }
end

let gather_thm acc (node : Doc.Node.t) =
  match node.ast with
  | None -> acc (* unparseable node *)
  | Some ast -> (
    match ast.ast_info with
    | None -> acc
    | Some info ->
      if check_thm info then
        let names = get_names info in
        { ThmDecl.names; node } :: acc
      else acc)

let get_theorems ~doc:{ Doc.nodes; _ } =
  List.fold_left nodes ~init:[] ~f:gather_thm |> List.rev

let vernac_timeout ~timeout (f : 'a -> 'b) (x : 'a) : 'b =
  match Control.timeout timeout f x with
  | None -> Exninfo.iraise (Exninfo.capture CErrors.Timeout)
  | Some x -> x

let interp =
  let intern = Vernacinterp.fs_intern in
  Vernacinterp.interp ~intern

let coq_interp_with_timeout ?timeout ~st cmd =
  let open Coq in
  let st = State.to_coq st in
  let cmd = Ast.to_coq cmd in
  (match timeout with
  | None -> interp ~st cmd
  | Some timeout -> vernac_timeout ~timeout (interp ~st) cmd)
  |> State.of_coq

let interp ?timeout ~token ~st cmd =
  Coq.Protect.eval cmd ~token ~f:(coq_interp_with_timeout ?timeout ~st)

let run_tac ~token ~st ?timeout tac =
  (* Parse tac, loc==FIXME *)
  let str = Gramlib.Stream.of_string tac in
  let str = Coq.Parsing.Parsable.make ?loc:None str in
  let ( let* ) x f = Coq.Protect.E.bind ~f x in
  let* ast = Coq.Parsing.parse ~token ~st str in
  match ast with
  | None -> Coq.Protect.E.ok None
  | Some ast ->
    interp ?timeout ~token ~st ast |> Coq.Protect.E.map ~f:Option.some

let pp_diag fmt (d : Lang.Diagnostic.t) =
  let open Stdlib in
  Format.fprintf fmt "@[%a@]"
    (Yojson.Safe.pretty_print ~std:true)
    (Fleche_lsp.JLang.Diagnostic.to_yojson d)

let pp_diags fmt dl =
  let open Stdlib in
  Format.fprintf fmt "@[%a@]" (Format.pp_print_list pp_diag) dl

(* completed == Yes && no diags errors *)
let completed_without_error ~(doc : Fleche.Doc.t) =
  let diags = Fleche.Doc.diags doc in
  let diags = List.filter ~f:Lang.Diagnostic.is_error diags in
  match doc.completed with
  | Yes _ -> if List.is_empty diags then None else Some diags
  | _ -> Some diags
