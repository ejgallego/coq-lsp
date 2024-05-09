(************************************************************************)
(* SerAPI: Coq interaction protocol with bidirectional serialization    *)
(************************************************************************)
(* Copyright 2016-2019 MINES ParisTech -- License LGPL 2.1+             *)
(* Copyright 2019-2023 Inria           -- License LGPL 2.1+             *)
(* Written by: Emilio J. Gallego Arias and others                       *)
(************************************************************************)

(* open Sexplib.Std *)
(* open Ppx_hash_lib.Std.Hash.Builtin *)
(* open Ppx_compare_lib.Builtin *)

(* let b x = Obj.magic x *)

(* These are all special ltac2 extensible objects, brrrr... *)
let register () =
  (* Ser_genarg.register_genser Tac2quote.wit_constr (b()); *)
  (* Ser_genarg.register_genser Tac2quote.wit_ident (b()); *)
  (* Ser_genarg.register_genser Tac2quote.wit_ltac1 (b()); *)
  (* Ser_genarg.register_genser Tac2quote.wit_ltac1val (b()); *)
  (* Ser_genarg.register_genser Tac2quote.wit_open_constr (b()); *)
  (* Ser_genarg.register_genser Tac2quote.wit_pattern (b()); *)
  (* Ser_genarg.register_genser Tac2quote.wit_preterm (b()); *)
  (* Ser_genarg.register_genser Tac2quote.wit_reference (b()); *)
  ()

let () = register ()
