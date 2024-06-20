(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016 MINES ParisTech                                       *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

open Sexplib

type 'a gxml = 'a Xml_datatype.gxml

val gxml_of_sexp : (Sexp.t -> 'a) -> Sexp.t -> 'a gxml
val sexp_of_gxml : ('a -> Sexp.t) -> 'a gxml -> Sexp.t
val gxml_of_yojson : (Yojson.Safe.t -> ('a, string) Result.result) -> Yojson.Safe.t -> ('a gxml, string) Result.result
val gxml_to_yojson : ('a -> Yojson.Safe.t) -> 'a gxml -> Yojson.Safe.t

type xml = Xml_datatype.xml

val xml_of_sexp : Sexp.t -> xml
val sexp_of_xml : xml -> Sexp.t
val xml_of_yojson : Yojson.Safe.t -> (xml, string) Result.result
val xml_to_yojson : xml -> Yojson.Safe.t
