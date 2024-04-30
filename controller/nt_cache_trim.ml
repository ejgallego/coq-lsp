module OCaml = struct
  (* Version using formatter instead of out_channel *)
  open Gc
  open Format

  let _print_stat c () =
    let st = stat () in
    fprintf c "minor_collections:      %d\n" st.minor_collections;
    fprintf c "major_collections:      %d\n" st.major_collections;
    fprintf c "compactions:            %d\n" st.compactions;
    fprintf c "forced_major_collections: %d\n" st.forced_major_collections;
    fprintf c "\n";
    let l1 = String.length (sprintf "%.0f" st.minor_words) in
    fprintf c "minor_words:    %*.0f\n" l1 st.minor_words;
    fprintf c "promoted_words: %*.0f\n" l1 st.promoted_words;
    fprintf c "major_words:    %*.0f\n" l1 st.major_words;
    fprintf c "\n";
    let l2 = String.length (sprintf "%d" st.top_heap_words) in
    fprintf c "top_heap_words: %*d\n" l2 st.top_heap_words;
    fprintf c "heap_words:     %*d\n" l2 st.heap_words;
    fprintf c "live_words:     %*d\n" l2 st.live_words;
    fprintf c "free_words:     %*d\n" l2 st.free_words;
    fprintf c "largest_free:   %*d\n" l2 st.largest_free;
    fprintf c "fragments:      %*d\n" l2 st.fragments;
    fprintf c "\n";
    fprintf c "live_blocks: %d\n" st.live_blocks;
    fprintf c "free_blocks: %d\n" st.free_blocks;
    fprintf c "heap_chunks: %d\n" st.heap_chunks

  let print_stat_simple c () =
    let st = stat () in
    let l2 = String.length (sprintf "%d" st.top_heap_words) in
    fprintf c "live:  %*d\n" l2 st.live_words;
    fprintf c "free:  %*d\n" l2 st.free_words;
    fprintf c "----------\n";
    ()
end

module M = Fleche.Memo
module LIO = Lsp.Io

let caches () =
  [ ("interp", M.Interp.all_freqs ())
  ; ("admit", M.Admit.all_freqs ())
  ; ("init", M.Init.all_freqs ())
  ; ("require", M.Require.all_freqs ())
  ]

let pp_cache fmt (name, freqs) =
  let zsum = List.filter (Int.equal 0) freqs in
  let pp_zsum fmt l = Format.fprintf fmt "{ 0-entries: %d }" (List.length l) in
  let fsum = Base.List.take freqs 20 in
  let pp_sep fmt () = Format.fprintf fmt ",@," in
  let pp_fsum = Format.(pp_print_list ~pp_sep pp_print_int) in
  Format.fprintf fmt "@[%s: %d | %a @[(%a)@]@]" name (List.length freqs) pp_zsum
    zsum pp_fsum fsum

let build_message () =
  let caches = caches () in
  Format.asprintf "@[Cache trim requested:@\n @[<v>%a@]@]"
    (Format.pp_print_list pp_cache)
    caches

let cache_trim () =
  let () = M.Interp.clear () in
  let () = M.Admit.clear () in
  let () = M.Init.clear () in
  let () = M.Require.clear () in
  ()

let gc_stats hd msg =
  let message =
    Format.asprintf "[%s] %s:@\n%a" hd msg OCaml.print_stat_simple ()
  in
  LIO.logMessage ~lvl:Info ~message

let full_major hd =
  gc_stats hd "before full major";
  Gc.full_major ();
  gc_stats hd "after full major";
  ()

let do_trim () =
  full_major "pre ";
  cache_trim ();
  let message = Format.asprintf "%s@\n---------@\n" "trimming" in
  LIO.logMessage ~lvl:Info ~message;
  full_major "post";
  ()

let notification () =
  let message = build_message () in
  LIO.logMessage ~lvl:Info ~message;
  do_trim ();
  ()
