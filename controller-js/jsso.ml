(*************************************************************************)
(* Copyright 2015-2019 MINES ParisTech -- Dual License LGPL 2.1+ / GPL3+ *)
(* Copyright 2018-2025 Shachar Itzhaky Technion -- LGPL 2.1+ / GPL3+     *)
(* Copyright 2019-2024 Inria           -- Dual License LGPL 2.1+ / GPL3+ *)
(* Copyright 2024-2025 Emilio J. Gallego Arias  -- LGPL 2.1+ / GPL3+     *)
(* Copyright 2025      CNRS                     -- LGPL 2.1+ / GPL3+     *)
(* Written by: Emilio J. Gallego Arias & coq-lsp contributors            *)
(*************************************************************************)
(* Rocq Language Server Protocol: Javascript utilities                   *)
(*************************************************************************)

open Js_of_ocaml

let rec obj_to_json (cobj : < .. > Js.t) : Yojson.Safe.t =
  let open Js in
  let open Js.Unsafe in
  let typeof_cobj = to_string (typeof cobj) in
  match typeof_cobj with
  | "string" -> `String (to_string @@ coerce cobj)
  | "boolean" -> `Bool (to_bool @@ coerce cobj)
  | "number" -> `Int (int_of_float @@ float_of_number @@ coerce cobj)
  | _ ->
    if instanceof cobj array_empty then
      `List Array.(to_list @@ map obj_to_json @@ to_array @@ coerce cobj)
    else if instanceof cobj Typed_array.arrayBuffer then
      `String (Typed_array.String.of_arrayBuffer @@ coerce cobj)
    else if instanceof cobj Typed_array.uint8Array then
      `String (Typed_array.String.of_uint8Array @@ coerce cobj)
      (* Careful in case we miss cases here, what about '{}' for example, we
         should also stop on functions? *)
    else if instanceof cobj Unsafe.global##._Object then
      Js.array_map
        (fun key -> (Js.to_string key, obj_to_json (Js.Unsafe.get cobj key)))
        (Js.object_keys cobj)
      |> Js.to_array |> Array.to_list
      |> fun al -> `Assoc al
    else if Js.Opt.(strict_equals (some cobj) null) then `Null
    else if Js.Optdef.(strict_equals (def cobj) undefined) then (
      Firebug.console##info "undefined branch!!!!";
      `Null)
    else (
      Firebug.console##error "failure in coq_lsp_worker:obj_to_json";
      Firebug.console##error cobj;
      Firebug.console##error (Json.output cobj);
      raise (Failure "coq_lsp_worker:obj_to_json"))

(* Old code, which is only useful for debug *)
(* let json_string = Js.to_string (Json.output cobj) in *)
(* Yojson.Safe.from_string json_string *)

let rec json_to_obj (cobj : < .. > Js.t) (json : Yojson.Safe.t) : < .. > Js.t =
  let open Js.Unsafe in
  let ofresh j = json_to_obj (obj [||]) j in
  match json with
  | `Bool b -> coerce @@ Js.bool b
  | `Null -> pure_js_expr "null"
  | `Assoc l ->
    List.iter (fun (p, js) -> set cobj p (ofresh js)) l;
    coerce @@ cobj
  | `List l -> coerce @@ Array.(Js.array @@ map ofresh (of_list l))
  | `Float f -> coerce @@ Js.number_of_float f
  | `String s -> coerce @@ Js.string s
  | `Int m -> coerce @@ Js.number_of_float (float_of_int m)
  | `Intlit s -> coerce @@ Js.number_of_float (float_of_string s)

let json_to_obj json = json_to_obj (Js.Unsafe.obj [||]) json
