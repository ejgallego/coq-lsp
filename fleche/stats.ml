(************************************************************************)
(* Coq Language Server Protocol                                         *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2022 Inria           -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)
(* Status: Experimental                                                 *)
(************************************************************************)

module Kind = struct
  type t =
    | Hashing
    | Parsing
    | Exec
end

type t =
  { time : float
  ; memory : float
  }

let stats : (Kind.t, t) Hashtbl.t = Hashtbl.create 1000
let z = { time = 0.0; memory = 0.0 }
let find kind = Hashtbl.find_opt stats kind |> Option.value ~default:z

module Global = struct
  type nonrec 'a stats = t
  type nonrec t = t * t * t

  let zero () = (z, z, z)
  let dump () = (find Kind.Hashing, find Kind.Parsing, find Kind.Exec)

  let restore (h, p, e) =
    Hashtbl.replace stats Kind.Hashing h;
    Hashtbl.replace stats Kind.Parsing p;
    Hashtbl.replace stats Kind.Exec e

  let get_f (h, p, e) ~kind =
    match kind with
    | Kind.Hashing -> h
    | Parsing -> p
    | Exec -> e

  let to_string (h, p, e) =
    Format.asprintf "hashing: %f | parsing: %f | exec: %f" h.time p.time e.time
end

let bump kind { time; memory } =
  let acc = find kind in
  let time = acc.time +. time in
  let memory = acc.memory +. memory in
  Hashtbl.replace stats kind { time; memory }

let time_and_mem f x =
  let { Gc.major_words = mw_prev; _ } = Gc.quick_stat () in
  let before = Unix.gettimeofday () in
  let v = f x in
  let after = Unix.gettimeofday () in
  let { Gc.major_words = mw_after; _ } = Gc.quick_stat () in
  let time = after -. before in
  let memory = mw_after -. mw_prev in
  (v, { time; memory })

let record ~kind ~f x =
  let res, stats = time_and_mem f x in
  bump kind stats;
  (res, stats)

let get_accumulated ~kind = find kind

let reset () =
  Hashtbl.remove stats Kind.Hashing;
  Hashtbl.remove stats Kind.Parsing;
  Hashtbl.remove stats Kind.Exec;
  ()

let mb = 1024 * 1024

let pp_words fmt w =
  (* Format is not working great for floating point values... *)
  let w = int_of_float w in
  let value, spec =
    if w < 1024 then (w, "w ")
    else if w < mb then (w / 1024, "Kw")
    else (w / mb, "Mw")
  in
  Format.fprintf fmt "@[%4d %s@]" value spec
