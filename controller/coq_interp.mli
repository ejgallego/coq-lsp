module Info : sig
  type 'a t =
    { res : 'a
    ; warnings : unit
    }
end

type 'a interp_result = 'a Info.t Coq_protect.R.t

val interp : st:Coq_state.t -> Coq_ast.t -> Coq_state.t interp_result
val marshal_in : (in_channel -> 'a) -> in_channel -> 'a interp_result

val marshal_out :
  (out_channel -> 'a -> unit) -> out_channel -> 'a interp_result -> unit
