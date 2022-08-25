module Path : sig
  type t
end

module Store : sig

  type t
  type path = string list
  type write_error

  val make : unit -> t Lwt.t
  val add : t -> path:path -> contents:string -> (unit, write_error) result Lwt.t
  val list : t -> string Lwt.t

end
