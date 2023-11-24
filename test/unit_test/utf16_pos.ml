(* Build with `ocamlbuild -pkg alcotest simple.byte` *)

open Coq

let testcases_x =
  [ ("aax", 2, true)
  ; ("  xoo", 2, true)
  ; ("0123", 4, false)
  ; ("  𝒞x", 4, true)
  ; ("  𝒞x𝒞", 4, true)
  ; ("  𝒞∫x", 5, true)
  ; ("  𝒞", 4, false)
  ; ("∫x.dy", 1, true)
  ]

(* The tests *)
let test_x () =
  List.iter
    (fun (s, i, b) ->
      let res = Utf8.get_byte_offset_from_utf16_pos s i in
      if b then
        let res = Option.map (fun i -> s.[i]) res in
        Alcotest.(check (option char)) "x present" (Some 'x') res
      else Alcotest.(check (option int)) "x present" None res)
    testcases_x

(* Run it *)
let () =
  let open Alcotest in
  run "Controller" [ ("utf16", [ test_case "Find the x" `Quick test_x ]) ]
