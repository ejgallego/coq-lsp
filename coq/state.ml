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
  let { synterp = { parsing = p1; system = ss1 }
      ; interp = { system = is1; lemmas = l1; program = g1; opaques = o1 }
      } =
    x
  in
  let { synterp = { parsing = p2; system = ss2 }
      ; interp = { system = is2; lemmas = l2; program = g2; opaques = o2 }
      } =
    y
  in
  if p1 == p2 && ss1 == ss2 && is1 == is2 && l1 == l2 && g1 == g2 && o1 == o2
  then 0
  else 1

let equal x y = compare x y = 0
let hash x = Hashtbl.hash x

let mode ~st =
  Option.map
    (fun _ -> Synterp.get_default_proof_mode ())
    st.Vernacstate.interp.lemmas

let parsing ~st = st.Vernacstate.synterp.parsing

module Proof_ = Proof

module Proof = struct
  type t = Vernacstate.LemmaStack.t

  let to_coq x = x
end

let lemmas ~st = st.Vernacstate.interp.lemmas

let program ~st =
  NeList.head st.Vernacstate.interp.program |> Declare.OblState.view

let drop_proofs ~st =
  let open Vernacstate in
  let interp =
    { st.interp with
      lemmas =
        Option.cata
          (fun s -> snd @@ Vernacstate.LemmaStack.pop s)
          None st.interp.lemmas
    }
  in
  { st with interp }

let in_state ~st ~f a =
  let f a =
    Vernacstate.unfreeze_full_state st;
    f a
  in
  Protect.eval ~f a

let in_stateM ~st ~f a =
  let open Protect.E.O in
  let* () = Protect.eval ~f:Vernacstate.unfreeze_full_state st in
  f a

let admit ~st () =
  let () = Vernacstate.unfreeze_full_state st in
  match st.Vernacstate.interp.lemmas with
  | None -> st
  | Some lemmas ->
    let pm = NeList.head st.Vernacstate.interp.program in
    let proof, lemmas = Vernacstate.(LemmaStack.pop lemmas) in
    let pm = Declare.Proof.save_admitted ~pm ~proof in
    let program = NeList.map_head (fun _ -> pm) st.Vernacstate.interp.program in
    let st = Vernacstate.freeze_full_state () in
    { st with interp = { st.interp with lemmas; program } }

let admit ~st = Protect.eval ~f:(admit ~st) ()

let admit_goal ~st () =
  let () = Vernacstate.unfreeze_full_state st in
  match st.Vernacstate.interp.lemmas with
  | None -> st
  | Some lemmas ->
    let f pf = Declare.Proof.by Proofview.give_up pf |> fst in
    let lemmas = Some (Vernacstate.LemmaStack.map_top ~f lemmas) in
    { st with interp = { st.interp with lemmas } }

let admit_goal ~st = Protect.eval ~f:(admit_goal ~st) ()
