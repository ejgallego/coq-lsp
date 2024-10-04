(************************************************************************)
(* Coq Language Server Protocol                                         *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2019-2023 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

module U = Yojson.Safe.Util
module L = Fleche.Io.Log

(* Conditionals *)
let option_default x d =
  match x with
  | None -> d
  | Some x -> x

let field name dict = List.(assoc name (U.to_assoc dict))
let ofield name dict = List.(assoc_opt name dict)
let ostring_field name dict = Option.map U.to_string (List.assoc_opt name dict)

let odict_field name dict =
  option_default
    U.(to_option to_assoc (option_default List.(assoc_opt name dict) `Null))
    []

(* Request Handling: The client expects a reply *)
let do_settings coq_lsp_options : unit =
  L.trace "settings" "setting server options:";
  L.trace_object "settings" (`Assoc coq_lsp_options);
  match Lsp.JFleche.Config.of_yojson (`Assoc coq_lsp_options) with
  | Ok v -> Fleche.Config.v := v
  | Error msg -> L.trace "CoqLspOption.of_yojson" "error: %s" msg

let check_client_version ~io client_version : unit =
  let server_version = Fleche.Version.server in
  L.trace "client_version" "%s" client_version;
  if String.(equal client_version "any" || equal client_version server_version)
  then () (* Version OK *)
  else
    Fleche.Io.Report.msg ~io ~lvl:Error
      "Incorrect client version: %s , expected %s." client_version
      server_version

(* Maybe this should be [cwd] ? *)
let default_workspace_root = "."
let parse_furi x = U.to_string x |> Lang.LUri.of_string |> Lang.LUri.File.of_uri

let parse_fpath ~io x =
  let path = U.to_string x in
  if Filename.is_relative path then
    Fleche.Io.Report.msg ~io ~lvl:Warning
      "rootPath is not absolute: %s . This is not robust, please use absolute \
       paths or rootURI"
      path;
  Lang.LUri.of_string ("file:///" ^ path) |> Lang.LUri.File.of_uri

let parse_null_or f = function
  | None -> None
  | Some l -> U.to_option f l

(* Poor's developer mapM *)
let rec result_map ls =
  match ls with
  | [] -> Result.ok []
  | r :: rs ->
    Result.bind r (fun x ->
        Result.bind (result_map rs) (fun xs -> Result.ok (x :: xs)))

let parse_furis l = List.map parse_furi l |> result_map
let parse_wf l = List.map (field "uri") (U.to_list l) |> parse_furis

let determine_workspace_root ~io ~params : string list =
  (* Careful: all paths fields can be present but have value `null` *)
  let rootPath = ofield "rootPath" params |> parse_null_or (parse_fpath ~io) in
  let rootUri = ofield "rootUri" params |> parse_null_or parse_furi in
  let wsFolders = ofield "workspaceFolders" params |> parse_null_or parse_wf in
  match (rootPath, rootUri, wsFolders) with
  | None, None, (None | Some (Ok [])) -> [ default_workspace_root ]
  | _, Some (Ok dir_uri), (None | Some (Ok [])) ->
    [ Lang.LUri.File.to_string_file dir_uri ]
  | Some (Ok dir_uri), None, (None | Some (Ok [])) ->
    [ Lang.LUri.File.to_string_file dir_uri ]
  | Some (Error msg), _, _ | _, Some (Error msg), _ | _, _, Some (Error msg) ->
    L.trace "init" "uri parsing failed: %s" msg;
    [ default_workspace_root ]
  | _, _, Some (Ok folders) -> List.map Lang.LUri.File.to_string_file folders

let determine_workspace_root ~io ~params =
  try determine_workspace_root ~io ~params
  with exn ->
    L.trace "init" "problem determining workspace root: %s"
      (Printexc.to_string exn);
    [ default_workspace_root ]

let get_trace ~params =
  match ostring_field "trace" params with
  | None -> Lsp.Io.TraceValue.Off
  | Some v -> (
    match Lsp.Io.TraceValue.of_string v with
    | Ok t -> t
    | Error e ->
      L.trace "trace" "invalid value: %s" e;
      Lsp.Io.TraceValue.Off)

let do_initialize ~io ~params =
  let dir = determine_workspace_root ~io ~params in
  let trace = get_trace ~params in
  Lsp.Io.set_trace_value trace;
  let coq_lsp_settings = odict_field "initializationOptions" params in
  do_settings coq_lsp_settings;
  check_client_version ~io !Fleche.Config.v.client_version;
  let client_capabilities = odict_field "capabilities" params in
  if Fleche.Debug.lsp_init then (
    L.trace "init" "client capabilities:";
    L.trace_object "init" (`Assoc client_capabilities));
  let capabilities =
    [ ("textDocumentSync", `Int 1)
    ; ("documentSymbolProvider", `Bool true)
    ; ("hoverProvider", `Bool true)
    ; ("codeActionProvider", `Bool true)
    ; ( "completionProvider"
      , `Assoc
          [ ("triggerCharacters", `List [ `String "\\" ])
          ; ("resolveProvider", `Bool false)
          ] )
    ; ("definitionProvider", `Bool true)
      (* EJGA: Disable this as we have no use case for now *)
      (* ; ("codeLensProvider", `Assoc []) *)
    ; ("selectionRangeProvider", `Bool true)
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
            ; ("version", `String Fleche.Version.server)
            ] )
      ]
  , dir )
