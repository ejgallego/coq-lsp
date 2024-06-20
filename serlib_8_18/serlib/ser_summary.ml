module Interp = struct

type frozen = Summary.Interp.frozen

let frozen_of_sexp x = Serlib_base.opaque_of_sexp ~typ:"Summary.Interp.frozen" x
let sexp_of_frozen x = Serlib_base.sexp_of_opaque ~typ:"Summary.Interp.frozen" x

end
