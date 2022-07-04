type t = Vernacstate.t

let summary_out oc (s : Summary.frozen) =
  let { Summary.summaries; ml_module } = s in
  Marshal.to_channel oc summaries [Closures];
  Marshal.to_channel oc ml_module [];
  ()

let summary_in ic : Summary.frozen =
  let summaries = Marshal.from_channel ic in
  let ml_module = Marshal.from_channel ic in
  { Summary.summaries; ml_module }

let system_out oc ((l : Lib.frozen), (s : Summary.frozen)) =
  (* Both parts of system have functional values !! Likely due to
     Lib.frozen having a Summary.frozen inside? *)
  Marshal.to_channel oc l [Closures];
  summary_out oc s;
  ()

let system_in ic : Vernacstate.System.t =
  let l : Lib.frozen = Marshal.from_channel ic in
  let s : Summary.frozen = summary_in ic in
  (l,s)

let marshal_out oc st =
  let { Vernacstate.parsing; system; lemmas; program; opaques; shallow } = st in
  Marshal.to_channel oc parsing [];
  system_out oc system;
  (* lemmas doesn't !! *)
  Marshal.to_channel oc lemmas [];
  Marshal.to_channel oc program [];
  Marshal.to_channel oc opaques [];
  Marshal.to_channel oc shallow [];
  ()

let marshal_in ic =
  let parsing = Marshal.from_channel ic in
  let system = system_in ic in
  let lemmas = Marshal.from_channel ic in
  let program = Marshal.from_channel ic in
  let opaques = Marshal.from_channel ic in
  let shallow = Marshal.from_channel ic in
  { Vernacstate.parsing; system; lemmas; program; opaques; shallow }

let of_coq x = x
let to_coq x = x

let compare x y = compare x y

let mode ~st =
  Option.map
    (fun _ -> Vernacinterp.get_default_proof_mode ())
    st.Vernacstate.lemmas

let parsing ~st = st.Vernacstate.parsing

let drop_proofs ~st =
  let open Vernacstate in
  { st with
    lemmas =
      Option.cata
        (fun s -> snd @@ Vernacstate.LemmaStack.pop s)
        None st.lemmas
  }

