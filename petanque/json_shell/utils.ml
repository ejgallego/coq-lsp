(* XXX: Flèche LSP backend already handles the conversion at the protocol
   level *)
let uri_of_string_exn uri =
  Lang.LUri.of_string uri |> Lang.LUri.File.of_uri |> Result.get_ok

let set_roots ~token ~debug ~roots =
  match roots with
  | [] -> ()
  | [ root ] | root :: _ -> (
    let root = uri_of_string_exn root in
    match Petanque.Shell.set_workspace ~token ~debug ~root with
    | Ok env ->
      (* hack until we fix the stuff *)
      let _ : Yojson.Safe.t = JAgent.Env.to_yojson env in
      ()
    | Error err ->
      Format.eprintf "Error: %s@\n%!" (Petanque.Agent.Error.to_string err))
