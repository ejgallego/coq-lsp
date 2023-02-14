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
(* Coq Language Server Protocol -- Requests                             *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2019-2023 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

type document_request =
  lines:string Array.t -> doc:Fleche.Doc.t -> Yojson.Safe.t

type position_request = doc:Fleche.Doc.t -> point:int * int -> Yojson.Safe.t

open Lsp.JFleche

let symbols ~lines ~(doc : Fleche.Doc.t) =
  let uri = doc.uri in
  let f loc id =
    let name = Names.Id.to_string id in
    let kind = 12 in
    let location =
      let range = Fleche.Coq_utils.to_range ~lines loc in
      { Location.uri; range }
    in
    SymInfo.(to_yojson { name; kind; location })
  in
  let ast = Fleche.Doc.asts doc in
  let slist = Coq.Ast.grab_definitions f ast in
  `List slist
