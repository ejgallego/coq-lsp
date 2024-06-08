(* Client wrap *)
module type Chans = sig
  val ic : in_channel
  val oc : Format.formatter
  val trace : ?verbose:string -> string -> unit
  val message : lvl:int -> message:string -> unit
end

(* Display incoming requests *)
let display_requests = false

let maybe_display_request method_ =
  if display_requests then Format.eprintf "received request: %s@\n%!" method_

let do_trace ~trace params =
  match Protocol.Trace.Params.of_yojson (`Assoc params) with
  | Ok { message; verbose } -> trace ?verbose message
  | Error _ -> ()

let do_message ~message params =
  match Protocol.Message.Params.of_yojson (`Assoc params) with
  | Ok { type_; message = msg } -> message ~lvl:type_ ~message:msg
  | Error _ -> ()

(* Read until we find a response *)
let rec read_response ~trace ~message ic =
  match Lsp.Io.read_message ic with
  | Some (Ok (Lsp.Base.Message.Response r)) -> Ok r
  | Some (Ok (Notification { method_; params }))
    when String.equal method_ Protocol.Trace.method_ ->
    do_trace ~trace params;
    read_response ~trace ~message ic
  | Some (Ok (Notification { method_; params }))
    when String.equal method_ Protocol.Message.method_ ->
    do_message ~message params;
    read_response ~trace ~message ic
  | Some (Ok (Request { method_; _ })) | Some (Ok (Notification { method_; _ }))
    ->
    maybe_display_request method_;
    read_response ~trace ~message ic
  | Some (Error err) -> Error err
  | None -> assert false (* not in our testing setup *)

let id_counter = ref 0

let get_id () =
  incr id_counter;
  !id_counter

module Wrap (R : Protocol.Request.S) (C : Chans) : sig
  val call : R.Params.t -> (R.Response.t, string) Result.t
end = struct
  let trace = C.trace
  let message = C.message

  let call params =
    let id = get_id () in
    let method_ = R.method_ in
    let params = Yojson.Safe.Util.to_assoc (R.Params.to_yojson params) in
    let request = Lsp.Base.Request.make ~id ~method_ ~params () in
    let () = Lsp.Io.send_message C.oc (Lsp.Base.Message.Request request) in
    read_response ~trace ~message C.ic |> fun r ->
    Result.bind r (function
      | Ok { id = _; result } -> R.Response.of_yojson result
      | Error { id = _; code = _; message; data = _ } -> Error message)
end

module S (C : Chans) = struct
  let init =
    let module M = Wrap (Protocol.SetWorkspace) (C) in
    M.call

  let start =
    let module M = Wrap (Protocol.Start) (C) in
    M.call

  let run_tac =
    let module M = Wrap (Protocol.RunTac) (C) in
    M.call

  let goals =
    let module M = Wrap (Protocol.Goals) (C) in
    M.call

  let premises =
    let module M = Wrap (Protocol.Premises) (C) in
    M.call
end
