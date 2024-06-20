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

type doc_id = Feedback.doc_id

val doc_id_of_sexp : Sexp.t -> doc_id
val sexp_of_doc_id : doc_id -> Sexp.t
val doc_id_of_yojson : Yojson.Safe.t -> (doc_id, string) Result.result
val doc_id_to_yojson : doc_id -> Yojson.Safe.t

type level = Feedback.level

val level_of_sexp : Sexp.t -> level
val sexp_of_level : level -> Sexp.t
val level_of_yojson : Yojson.Safe.t -> (level, string) Result.result
val level_to_yojson : level -> Yojson.Safe.t

type route_id = Feedback.route_id
val route_id_of_sexp : Sexp.t -> route_id
val sexp_of_route_id : route_id -> Sexp.t
val route_id_of_yojson : Yojson.Safe.t -> (route_id, string) Result.result
val route_id_to_yojson : route_id -> Yojson.Safe.t

type feedback_content = Feedback.feedback_content

val feedback_content_of_sexp : Sexp.t -> feedback_content
val sexp_of_feedback_content : feedback_content -> Sexp.t
val feedback_content_of_yojson : Yojson.Safe.t -> (feedback_content, string) Result.result
val feedback_content_to_yojson : feedback_content -> Yojson.Safe.t

type feedback = Feedback.feedback

val feedback_of_sexp : Sexp.t -> feedback
val sexp_of_feedback : feedback -> Sexp.t
val feedback_of_yojson : Yojson.Safe.t -> (feedback, string) Result.result
val feedback_to_yojson : feedback -> Yojson.Safe.t
