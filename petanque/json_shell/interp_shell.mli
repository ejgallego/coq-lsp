(************************************************************************)
(* Coq Petanque                                                         *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2019-2024 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(************************************************************************)

module Lsp = Fleche_lsp

(* API for regular pet-server style shells *)
type doc_handler =
     token:Coq.Limits.Token.t
  -> uri:Lang.LUri.File.t
  -> Fleche.Doc.t Petanque.Agent.R.t

val interp :
     fn:doc_handler
  -> token:Coq.Limits.Token.t
  -> Lsp.Base.Message.t
  -> Lsp.Base.Message.t option
