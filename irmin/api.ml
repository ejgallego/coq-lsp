open Lwt.Syntax

let pp_sep = Format.pp_print_cut
let rec pp_list fmt pp l = match l with
  | [] -> Lwt.return ()
  | [x] -> pp fmt x
  | x :: xs ->
    let* () = pp fmt x in
    pp_sep fmt ();
    pp_list fmt pp xs

module Path = struct
  type t = string
end

module Irmin_store = Irmin_mem.KV.Make(Irmin.Contents.String)

module Store = struct

  type t = Irmin_store.t
  type path = Irmin_store.path
  type write_error = Irmin_store.write_error

  let make () =
    let conf = Irmin_mem.config () in
    let* repo = Irmin_store.Repo.v conf in
    Irmin_store.main repo

  let add st ~path ~contents =
    let author = "Emilio" in
    let message = "try 1" in
    let date = Int64.of_int 202932 in
    let info () = Irmin_store.Info.v ~author ~message date in
    Irmin_store.set ~info st path contents

  let rec print_tree fmt (path, tree) : unit Lwt.t =
    Format.fprintf fmt "@[[%s] ~> @[<v>" path;
    let* ne = Irmin_store.Tree.list tree [] in
    let+ () = pp_list fmt print_tree ne in
    Format.fprintf fmt "@]@]"

  let list st =
    let* tree = Irmin_store.tree st in
    let _ = Format.flush_str_formatter () in
    let+ () = print_tree Format.str_formatter ("/", tree) in
    Format.flush_str_formatter ()

end
