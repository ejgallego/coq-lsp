type t = Vernacstate.t

(* EJGA: This requires patches to Coq, they are in the lsp_debug branch

   let any_out oc (a : Summary.Frozen.any) = (* let (Summary.Frozen.Any (tag,
   _value)) = a in *) (* let name = Summary.Dyn.repr tag in *) (*
   Lsp.Io.log_error "marshall" name; *) Marshal.to_channel oc a []

   let _frozen_out oc (s : Summary.Frozen.t) = Summary.Frozen.iter (any_out oc)
   s

   let summary_out oc (s : Summary.frozen) = let { Summary.summaries; ml_module
   } = s in (* frozen_out oc summaries; *) Marshal.to_channel oc summaries [];
   Marshal.to_channel oc ml_module []; ()

   let summary_in ic : Summary.frozen = let summaries = Marshal.from_channel ic
   in let ml_module = Marshal.from_channel ic in { Summary.summaries; ml_module
   }

   let system_out oc ((l : Lib.frozen), (s : Summary.frozen)) = (* Both parts of
   system have functional values !! Likely due to Lib.frozen having a
   Summary.frozen inside? *) Marshal.to_channel oc l [ Closures ]; summary_out
   oc s; ()

   let system_in ic : Vernacstate.System.t = let l : Lib.frozen =
   Marshal.from_channel ic in let s : Summary.frozen = summary_in ic in (l, s)

   let _marshal_out oc st = let { Vernacstate.parsing; system; lemmas; program;
   opaques; shallow } = st in Marshal.to_channel oc parsing []; system_out oc
   system; (* lemmas doesn't !! *) Marshal.to_channel oc lemmas [];
   Marshal.to_channel oc program []; Marshal.to_channel oc opaques [];
   Marshal.to_channel oc shallow []; ()

   let _marshal_in ic = let parsing = Marshal.from_channel ic in let system =
   system_in ic in let lemmas = Marshal.from_channel ic in let program =
   Marshal.from_channel ic in let opaques = Marshal.from_channel ic in let
   shallow = Marshal.from_channel ic in { Vernacstate.parsing; system; lemmas;
   program; opaques; shallow } *)

let marshal_in ic : t = Marshal.from_channel ic
let marshal_out oc st = Marshal.to_channel oc st []
let of_coq x = x
let to_coq x = x

(* let compare x y = compare x y *)
let compare (x : t) (y : t) =
  let open Vernacstate in
  let { parsing = p1
      ; system = s1
      ; lemmas = l1
      ; program = g1
      ; opaques = o1
      ; shallow = h1
      } =
    x
  in
  let { parsing = p2
      ; system = s2
      ; lemmas = l2
      ; program = g2
      ; opaques = o2
      ; shallow = h2
      } =
    y
  in
  if p1 == p2 && s1 == s2 && l1 == l2 && g1 == g2 && o1 == o2 && h1 == h2 then 0
  else 1

let equal x y = compare x y = 0
let hash x = Hashtbl.hash x

let mode ~st =
  Option.map
    (fun _ -> Vernacinterp.get_default_proof_mode ())
    st.Vernacstate.lemmas

let parsing ~st = st.Vernacstate.parsing

module Proof = struct
  type t = Vernacstate.LemmaStack.t

  let to_coq x = x
end

let lemmas ~st = st.Vernacstate.lemmas

let drop_proofs ~st =
  let open Vernacstate in
  { st with
    lemmas =
      Option.cata (fun s -> snd @@ Vernacstate.LemmaStack.pop s) None st.lemmas
  }

let in_state ~st ~f a =
  let f a =
    Vernacstate.unfreeze_interp_state st;
    f a
  in
  Protect.eval ~pure:true ~f a

let admit ~st =
  let () = Vernacstate.unfreeze_interp_state st in
  match st.Vernacstate.lemmas with
  | None -> st
  | Some lemmas ->
    let pm = NeList.head st.Vernacstate.program in
    let proof, lemmas = Vernacstate.(LemmaStack.pop lemmas) in
    let pm = Declare.Proof.save_admitted ~pm ~proof in
    let program = NeList.map_head (fun _ -> pm) st.Vernacstate.program in
    let st = Vernacstate.freeze_interp_state ~marshallable:false in
    { st with lemmas; program }

(* TODO: implement protect once error recovery supports a failing recovery
   execution *)
(* let admit ~st = Protect.eval ~f:(admit ~st) () *)
