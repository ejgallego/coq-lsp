(************************************************************************)
(* Coq Language Server Protocol                                         *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2019-2023 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

module U = Yojson.Safe.Util
module LIO = Lsp.Io

(* Conditionals *)
let option_default x d =
  match x with
  | None -> d
  | Some x -> x

let option_cata f d x =
  match x with
  | None -> d
  | Some x -> f x

let string_field name dict = U.to_string (List.assoc name (U.to_assoc dict))
let ostring_field name dict = Option.map U.to_string (List.assoc_opt name dict)
let olist_field name dict = Option.map U.to_list (List.assoc_opt name dict)

let odict_field name dict =
  option_default
    U.(to_option to_assoc (option_default List.(assoc_opt name dict) `Null))
    []

(* Request Handling: The client expects a reply *)
let do_client_options coq_lsp_options : unit =
  LIO.trace "init" "custom client options:";
  LIO.trace_object "init" (`Assoc coq_lsp_options);
  match Lsp.JFleche.Config.of_yojson (`Assoc coq_lsp_options) with
  | Ok v -> Fleche.Config.v := v
  | Error msg -> LIO.trace "CoqLspOption.of_yojson error: " msg

let check_client_version client_version : unit =
  LIO.trace "client_version" client_version;
  if String.(equal client_version "any" || equal client_version Version.server)
  then () (* Version OK *)
  else
    let message =
      Format.asprintf "Incorrect client version: %s , expected %s."
        client_version Version.server
    in
    LIO.logMessage ~lvl:1 ~message

let default_workspace_root = "."
let parse_furi x = Lang.LUri.of_string x |> Lang.LUri.File.of_uri

(* Poor man mapM *)
let rec result_map ls =
  match ls with
  | [] -> Result.ok []
  | r :: rs ->
    Result.bind r (fun x ->
        Result.bind (result_map rs) (fun xs -> Result.ok (x :: xs)))

let parse_furis l = List.map parse_furi l |> result_map
let parse_wf l = List.map (string_field "uri") l |> parse_furis

let determine_workspace_root ~params : string list =
  let rootPath = ostring_field "rootPath" params |> Option.map parse_furi in
  let rootUri = ostring_field "rootUri" params |> Option.map parse_furi in
  (* XXX: enable when we advertise workspace folders support in the server *)
  let wsFolders =
    olist_field "workspaceFolders" params |> Option.map parse_wf
  in
  match (rootPath, rootUri, wsFolders) with
  | None, None, None -> [ default_workspace_root ]
  | _, Some (Ok dir_uri), None -> [ Lang.LUri.File.to_string_file dir_uri ]
  | Some (Ok dir_uri), None, None -> [ Lang.LUri.File.to_string_file dir_uri ]
  | Some (Error msg), _, _ | _, Some (Error msg), _ | _, _, Some (Error msg) ->
    LIO.trace "init" ("uri parsing failed: " ^ msg);
    [ default_workspace_root ]
  | _, _, Some (Ok folders) -> List.map Lang.LUri.File.to_string_file folders

let do_initialize ~params =
  let dir = determine_workspace_root ~params in
  let trace =
    ostring_field "trace" params
    |> option_cata LIO.TraceValue.of_string LIO.TraceValue.Off
  in
  LIO.set_trace_value trace;
  let coq_lsp_options = odict_field "initializationOptions" params in
  do_client_options coq_lsp_options;
  check_client_version !Fleche.Config.v.client_version;
  let client_capabilities = odict_field "capabilities" params in
  if Fleche.Debug.lsp_init then (
    LIO.trace "init" "client capabilities:";
    LIO.trace_object "init" (`Assoc client_capabilities));
  let capabilities =
    [ ("textDocumentSync", `Int 1)
    ; ("documentSymbolProvider", `Bool true)
    ; ("hoverProvider", `Bool true)
    ; ("codeActionProvider", `Bool false)
    ; ( "completionProvider"
      , `Assoc
          [ ("triggerCharacters", `List [ `String "\\" ])
          ; ("resolveProvider", `Bool false)
          ] )
    ; ("definitionProvider", `Bool true)
    ; ("codeLensProvider", `Assoc [])
    ; ( "workspace"
      , `Assoc
          [ ( "workspaceFolders"
            , `Assoc
                [ ("supported", `Bool true)
                ; ("changeNotifications", `Bool true)
                ] )
          ] )
    ]
  in
  ( `Assoc
      [ ("capabilities", `Assoc capabilities)
      ; ( "serverInfo"
        , `Assoc
            [ ("name", `String "coq-lsp (C) Inria 2022-2023")
            ; ("version", `String Version.server)
            ] )
      ]
  , dir )
