open Petanque

(* We handle the conversion here, at the protocol level *)
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
