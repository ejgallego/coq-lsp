open Sexplib.Conv

module Names = Ser_names

(* type vernac_type =
 *   [%import: Vernacextend.vernac_type]
 *   [@@deriving sexp] *)
type vernac_keep_as =
  [%import: Vernacextend.vernac_keep_as]
  [@@deriving sexp]
and vernac_qed_type =
  [%import: Vernacextend.vernac_qed_type]
  [@@deriving sexp]
and vernac_when =
  [%import: Vernacextend.vernac_when]
  [@@deriving sexp]
and vernac_start =
  [%import: Vernacextend.vernac_start]
  [@@deriving sexp]
and vernac_sideff_type =
  [%import: Vernacextend.vernac_sideff_type]
  [@@deriving sexp]
and opacity_guarantee =
  [%import: Vernacextend.opacity_guarantee]
  [@@deriving sexp]
and solving_tac =
  [%import: Vernacextend.solving_tac]
  [@@deriving sexp]
and anon_abstracting_tac =
  [%import: Vernacextend.anon_abstracting_tac]
  [@@deriving sexp]
and proof_block_name =
  [%import: Vernacextend.proof_block_name]
  [@@deriving sexp]
