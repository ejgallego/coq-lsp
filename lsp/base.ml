(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(************************************************************************)
(* Coq Language Server Protocol                                         *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)
(* Status: Experimental                                                 *)
(************************************************************************)

(* This file contains some coq-specific commands, we should instead
   functorialize it so we can share with other OCaml-specific tools *)

(* Whether to send extended lsp messages *)
let std_protocol = ref true

module J = Yojson.Safe

let _mk_extra l = if !std_protocol then [] else l

(* Ad-hoc parsing for file:///foo... *)
let _parse_uri str =
  let l = String.length str - 7 in
  String.(sub str 7 l)

let mk_reply ~id ~result =
  `Assoc [ ("jsonrpc", `String "2.0"); ("id", `Int id); ("result", result) ]

let mk_notification ~method_ ~params =
  `Assoc
    [ ("jsonrpc", `String "2.0")
    ; ("method", `String method_)
    ; ("params", `Assoc params)
    ]

(* let json_of_goal g = let pr_hyp (s,(_,t)) = `Assoc ["hname", `String s;
   "htype", `String (Format.asprintf "%a" Print.pp_term (Bindlib.unbox t))] in
   let open Proofs in let j_env = List.map pr_hyp g.g_hyps in `Assoc [ "gid",
   `Int g.g_meta.meta_key ; "hyps", `List j_env ; "type", `String
   (Format.asprintf "%a" Print.pp_term g.g_type)]

   let json_of_thm thm = let open Proofs in match thm with | None -> `Null |
   Some thm -> `Assoc [ "goals", `List List.(map json_of_goal thm.t_goals) ] *)

let mk_range { Fleche.Types.Range.start; _end } : J.t =
  `Assoc
    [ ( "start"
      , `Assoc
          [ ("line", `Int start.line); ("character", `Int start.character) ] )
    ; ( "end"
      , `Assoc [ ("line", `Int _end.line); ("character", `Int _end.character) ]
      )
    ]

(* let mk_diagnostic ((p : Pos.pos), (lvl : int), (msg : string), (thm :
   Proofs.theorem option)) : J.json = *)
let mk_diagnostic
    ( (r : Fleche.Types.Range.t)
    , (lvl : int)
    , (msg : string)
    , (_thm : unit option) ) : J.t =
  (* let goal = json_of_thm thm in *)
  let range = mk_range r in
  `Assoc
    [ (* mk_extra ["goal_info", goal] @ *)
      ("range", range)
    ; ("severity", `Int lvl)
    ; ("message", `String msg)
    ]

let mk_diagnostics ~uri ~version ld : J.t =
  mk_notification ~method_:"textDocument/publishDiagnostics"
    ~params:
      [ ("uri", `String uri)
      ; ("version", `Int version)
      ; ("diagnostics", `List List.(map mk_diagnostic ld))
      ]
