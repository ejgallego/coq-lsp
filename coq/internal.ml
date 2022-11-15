module type Conv = sig
  type t

  module Internal : sig
    type coq

    val of_coq : coq -> t
    val to_coq : t -> coq
  end
end

module Make (S : sig
  type coq
end) : Conv with type Internal.coq = S.coq = struct
  module Internal = struct
    type coq = S.coq

    let of_coq x = x
    let to_coq x = x
  end

  type t = S.coq
end
