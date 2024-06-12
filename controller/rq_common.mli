(************************************************************************)
(* Coq Language Server Protocol -- Common requests routines             *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2019-2023 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

(* Contents utils, should be moved to Contents.t , they mainly handle character
   enconding conversiong between protocol and prover positions, if needed *)

val get_id_at_point :
  contents:Fleche.Contents.t -> point:int * int -> string option

val get_char_at_point :
  prev:bool -> contents:Fleche.Contents.t -> point:int * int -> char option

(* Get both the uchar and its utf-8 string representation *)
val get_uchar_at_point :
     prev:bool
  -> contents:Fleche.Contents.t
  -> point:int * int
  -> (Uchar.t * string) option
