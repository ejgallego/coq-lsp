(************************************************************************)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1+ / GPL3+     *)
(* Copyright 2019-2024 Inria      -- Dual License LGPL 2.1+ / GPL3+     *)
(* Copyright 2024-2025 Emilio J. Gallego Arias -- LGPL 2.1+ / GPL3+     *)
(* Copyright 2025      CNRS                    -- LGPL 2.1+ / GPL3+     *)
(* Written by: Emilio J. Gallego Arias & coq-lsp contributors           *)
(************************************************************************)
(* Flèche => Extensible AST analysis                                    *)
(************************************************************************)

(* Located names *)
module LocNames = struct
  type a = Names.Name.t CAst.t list
  let name = "located defined identifiers in AST"

  let default _ = Some []

  let fold_list = List.concat
  let fold_option = function None -> [] | Some a -> a
  let fold_pair (l1, l2) = List.append l1 l2
end

module NameAnalysis = Ser_genarg.Analyzer.Make(LocNames)
