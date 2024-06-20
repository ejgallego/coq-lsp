(* open Serlib *)
(* open Ltac2_plugin *)

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
