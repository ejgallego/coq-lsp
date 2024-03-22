open Cmdliner

(** example input / output sequence:

{{{

["Start",{"uri":"file:///home/egallego/research/coq-lsp/examples/ex0.v","thm":"addnC"}]
["Start",131266756246311]

["Run_tac", {"st": 131266756246311, "tac": "induction n."}]
["Run_tac",131266894677423]

["Run_tac", {"st": 131266894677423, "tac": "simpl."}]
["Run_tac",131266896660087]

["Run_tac", {"st": 131266896660087, "tac": "auto."}]
["Run_tac",131266896448871]

}}}
 *)

let rec loop () : unit =
  try
    let line = read_line () in
    let json = Yojson.Safe.from_string line in
    match Protocol.Command.of_yojson json with
    | Error msg -> raise (Failure msg)
    | Ok cmd ->
      let answer = Interp.interp cmd in
      Format.printf "@[%s@]@\n%!"
        (Yojson.Safe.to_string (Protocol.Answer.to_yojson answer));
      loop ()
  with
  | End_of_file -> ()
  (* if the input does not match the format. *)
  | Scanf.Scan_failure msg
  (* if a conversion to a number is not possible. *)
  | Failure msg
  (* if the format string is invalid. *)
  | Invalid_argument msg ->
    Format.eprintf "error: %s" msg;
    ()

let pet_main () = loop ()

let pet_cmd : unit Cmd.t =
  let doc = "Petanque Coq Environment" in
  let man =
    [ `S "DESCRIPTION"
    ; `P "Petanque Coq Environment"
    ; `S "USAGE"
    ; `P "See the documentation on the project's webpage for more information"
    ]
  in
  let version = Fleche.Version.server in
  let pet_term =
    Term.(const pet_main $ const ())
    (* const pet_main $ roots $ display $ debug $ plugins $ file $ coqlib *)
    (* $ coqcorelib $ ocamlpath $ rload_path $ load_path $ rifrom) *)
  in
  Cmd.(v (Cmd.info "pet" ~version ~doc ~man) pet_term)

let main () =
  let ecode = Cmd.eval pet_cmd in
  exit ecode

let () = main ()
