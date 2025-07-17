(************************************************************************)
(* Flèche / coq-lsp                                                     *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2019-2024 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2024-2025 Emilio J. Gallego Arias -- LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias & coq-lsp contributors           *)
(************************************************************************)

(** Use:

    {v
make && dune exec -- fcc --plugin=coq-lsp.plugin.count_genargs test/serlib/genarg/clear.v
    v} *)

module Lsp = Fleche_lsp
open Fleche

module GAT = struct
  type a = int

  let name = "count_genarg"
  let default _ = Some 666
  let fold_list = List.fold_left ( + ) 0

  let fold_option = function
    | Some x -> x
    | None -> 0

  let fold_pair (n1, n2) = n1 + n2
end

module CGA = Serlib.Ser_genarg.Analyzer.Make (GAT)

let count (ast : Vernacexpr.vernac_control) =
  match ast.v.expr with
  | VernacExtend (_name, genarg) ->
    List.fold_left (fun acc ga -> acc + CGA.analyze ga) 1 genarg
  | _ -> 0

let count_genargs (ast : Doc.Node.Ast.t) : int =
  let ast = Coq.Ast.to_coq ast.v in
  count ast

let pp fmt x = Format.pp_print_int fmt x

let count_genargs ~io ~token:_ ~(doc : Doc.t) =
  let uri = doc.uri in
  let uri_str = Lang.LUri.File.to_string_uri uri in
  let lvl = Io.Level.Info in
  Io.Report.msg ~io ~lvl "[count_genargs plugin] dumping count for %s ..."
    uri_str;
  let asts = Doc.asts doc in
  (* Output json *)
  let res = List.map count_genargs asts in
  Format.(printf "@[<v>%a@]@\n%!" (pp_print_list pp) res);
  Io.Report.msg ~io ~lvl "[count_genargs plugin] count for %s was completed!"
    uri_str;
  ()

let main () = Theory.Register.Completed.add count_genargs
let () = main ()
