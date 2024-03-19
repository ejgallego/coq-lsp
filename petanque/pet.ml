open Cmdliner

(* We handle the conversion here, at the protocol level *)
module State : sig
  type t = Agent.State.t [@@deriving yojson]
end = struct
  type t = Agent.State.t
  type _t = int [@@deriving yojson]

  module Memo = Hashtbl.Make (Int)

  let memo = Memo.create 1000

  let dump_memo () =
    let keys = Memo.to_seq_keys memo |> List.of_seq in
    Format.(eprintf "@[size: %d@]@\n%!" (List.length keys));
    Format.(eprintf "@[<v>%a@]@\n%!" (pp_print_list pp_print_int) keys)

  let mk_id s : int = Obj.(magic (repr s)) * 2

  let _dump_goals s =
    let id = mk_id s in
    let goals = Agent.State.goals s |> Option.default "no goals" in
    Format.eprintf "@[seen state: %d@ and goals: %s\n@]%!" id goals

  let of_agent (s : Agent.State.t) : int =
    let id = mk_id s in
    let () = Memo.add memo id s in
    (* dump_memo (); *)
    id

  let to_agent (id : int) : Agent.State.t =
    try Memo.find memo id
    with Not_found ->
      dump_memo ();
      raise Not_found

  let of_yojson json = _t_of_yojson json |> Result.map to_agent
  let to_yojson st : Yojson.Safe.t = of_agent st |> _t_to_yojson
end

module Command = struct
  type t =
    | Start of
        { uri : string
        ; thm : string
        }
    | Run_tac of
        { st : State.t
        ; tac : string
        }
    | Goals of { st : State.t }
  [@@deriving yojson]
end

module Answer = struct
  type t =
    | Start of State.t option
    | Run_tac of State.t option
    | Goals of string option
  [@@deriving yojson]
end

let interp (c : Command.t) : Answer.t =
  match c with
  | Start { uri; thm } ->
    let uri =
      Lang.LUri.of_string uri |> Lang.LUri.File.of_uri |> Result.get_ok
    in
    let st = Agent.start ~uri ~thm in
    Answer.Start st
  | Run_tac { st; tac } ->
    let st = Agent.run_tac ~st ~tac in
    Answer.Run_tac st
  | Goals { st } ->
    let goals = Agent.State.goals st in
    Answer.Goals goals

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
    match Command.of_yojson json with
    | Error msg -> raise (Failure msg)
    | Ok cmd ->
      let answer = interp cmd in
      Format.printf "@[%s@]@\n%!"
        (Yojson.Safe.to_string (Answer.to_yojson answer));
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
