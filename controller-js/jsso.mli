open Js_of_ocaml

(* Object to Yojson converter *)
val obj_to_json : < .. > Js.t -> Yojson.Safe.t
val json_to_obj : Yojson.Safe.t -> < .. > Js.t
