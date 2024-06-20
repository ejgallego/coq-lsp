type frozen = Summary.frozen

let frozen_of_sexp x = Serlib_base.opaque_of_sexp ~typ:"Summary.frozen" x
let sexp_of_frozen x = Serlib_base.sexp_of_opaque ~typ:"Summary.frozen" x
