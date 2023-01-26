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

let ostring_field name dict = Option.map U.to_string (List.assoc_opt name dict)

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

let do_initialize ~params =
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
    ; ("completionProvider", `Assoc [])
    ; ("codeActionProvider", `Bool false)
    ]
  in
  `Assoc
    [ ("capabilities", `Assoc capabilities)
    ; ( "serverInfo"
      , `Assoc
          [ ("name", `String "coq-lsp (C) Inria 2022-2023")
          ; ("version", `String Version.server)
          ] )
    ]
