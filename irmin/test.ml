open Lwt.Syntax
open Storage

let main =
  let* s = Api.Store.make () in
  let* _r = Api.Store.add s ~path:["emilio"] ~contents:"this is test 1" in
  let* _r = Api.Store.add s ~path:["emilio";"ana"] ~contents:"this is a test 5" in
  let* _r = Api.Store.add s ~path:["borja"] ~contents:"this is a test 2" in
  let* _r = Api.Store.add s ~path:["mama"] ~contents:"this is a test 6" in
  let* _r = Api.Store.add s ~path:["mama";"papa"] ~contents:"this is a test 3" in
  let* _r = Api.Store.add s ~path:["mama";"borja"] ~contents:"this is a test 4" in
  let* keys = Api.Store.list s in
  Format.eprintf "@[%s@]@\n%!" keys;
  Lwt.return ()

let () = Lwt_main.run main
