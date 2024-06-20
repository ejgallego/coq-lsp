type options =
  { omit_loc : bool
  ; omit_att : bool
  ; omit_env : bool
  ; exn_on_opaque : bool
  }

let init ~options =
  Ser_loc.omit_loc  := options.omit_loc;
  Ser_cAst.omit_att := options.omit_att;
  Serlib_base.exn_on_opaque := options.exn_on_opaque;
  Ser_environ.abstract_env := options.omit_env;
  ()
