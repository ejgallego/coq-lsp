module G = Serapi.Serapi_goals

module Info : sig
  type 'a t =
    { res : 'a
    ; goal : Pp.t G.reified_goal G.ser_goals option
    ; feedback : Pp.t list
    }
end

type 'a interp_result = 'a Info.t Coq_protect.R.t

val interp :
     st:Coq_state.t
  -> fb_queue:Pp.t list ref
  -> Coq_ast.t
  -> Coq_state.t interp_result

val marshal_in : (in_channel -> 'a) -> in_channel -> 'a interp_result

val marshal_out :
  (out_channel -> 'a -> unit) -> out_channel -> 'a interp_result -> unit
