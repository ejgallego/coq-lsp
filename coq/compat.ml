(* Compatibility file *)

module Ocaml_413 = struct
  module String = struct
    open String

    let starts_with ~prefix s =
      let len_s = length s
      and len_pre = length prefix in
      let rec aux i =
        if i = len_pre then true
        else if unsafe_get s i <> unsafe_get prefix i then false
        else aux (i + 1)
      in
      len_s >= len_pre && aux 0
  end
end

module Ocaml_414 = struct
  module In_channel = struct
    (* 4.14 can do this: In_channel.with_open_bin file In_channel.input_all, so
       we better copy the code XD *)

    let with_open openfun s f =
      let ic = openfun s in
      Fun.protect ~finally:(fun () -> Stdlib.close_in_noerr ic) (fun () -> f ic)

    let with_open_bin s f = with_open Stdlib.open_in_bin s f
    let with_open_text s f = with_open Stdlib.open_in s f

    (* Read up to [len] bytes into [buf], starting at [ofs]. Return total bytes
       read. *)
    let read_upto ic buf ofs len =
      let rec loop ofs len =
        if len = 0 then ofs
        else
          let r = Stdlib.input ic buf ofs len in
          if r = 0 then ofs else loop (ofs + r) (len - r)
      in
      loop ofs len - ofs

    let ensure buf ofs n =
      let len = Bytes.length buf in
      if len >= ofs + n then buf
      else
        let new_len = ref len in
        while !new_len < ofs + n do
          new_len := (2 * !new_len) + 1
        done;
        let new_len = !new_len in
        let new_len =
          if new_len <= Sys.max_string_length then new_len
          else if ofs < Sys.max_string_length then Sys.max_string_length
          else
            failwith
              "In_channel.input_all: channel content is larger than maximum \
               string length"
        in
        let new_buf = Bytes.create new_len in
        Bytes.blit buf 0 new_buf 0 ofs;
        new_buf

    let input_all ic =
      let chunk_size = 65536 in
      (* IO_BUFFER_SIZE *)
      let initial_size =
        try Stdlib.in_channel_length ic - Stdlib.pos_in ic
        with Sys_error _ -> -1
      in
      let initial_size =
        if initial_size < 0 then chunk_size else initial_size
      in
      let initial_size =
        if initial_size <= Sys.max_string_length then initial_size
        else Sys.max_string_length
      in
      let buf = Bytes.create initial_size in
      let nread = read_upto ic buf 0 initial_size in
      if nread < initial_size then
        (* EOF reached, buffer partially filled *)
        Bytes.sub_string buf 0 nread
      else
        (* nread = initial_size, maybe EOF reached *)
        match Stdlib.input_char ic with
        | exception End_of_file ->
          (* EOF reached, buffer is completely filled *)
          Bytes.unsafe_to_string buf
        | c ->
          (* EOF not reached *)
          let rec loop buf ofs =
            let buf = ensure buf ofs chunk_size in
            let rem = Bytes.length buf - ofs in
            (* [rem] can be < [chunk_size] if buffer size close to
               [Sys.max_string_length] *)
            let r = read_upto ic buf ofs rem in
            if r < rem then (* EOF reached *)
              Bytes.sub_string buf 0 (ofs + r)
            else (* r = rem *)
              loop buf (ofs + rem)
          in
          let buf = ensure buf nread (chunk_size + 1) in
          Bytes.set buf nread c;
          loop buf (nread + 1)
  end

  module Out_channel = struct
    let with_open openfun s f =
      let oc = openfun s in
      Fun.protect
        ~finally:(fun () -> Stdlib.close_out_noerr oc)
        (fun () -> f oc)

    let with_open_bin s f = with_open Stdlib.open_out_bin s f
  end
end

module Result = struct
  include Result

  module O = struct
    let ( let+ ) r f = map f r
    let ( let* ) r f = bind r f
  end

  let split = function
    | Ok (x1, x2) -> (Ok x1, Ok x2)
    | Error err -> (Error err, Error err)

  let pp pp_r pp_e fmt = function
    | Ok r -> Format.fprintf fmt "@[Ok: @[%a@]@]" pp_r r
    | Error e -> Format.fprintf fmt "@[Error: @[%a@]@]" pp_e e
end

let format_to_file ~file ~f x =
  let open Ocaml_414 in
  Out_channel.with_open_bin file (fun oc ->
      let of_fmt = Format.formatter_of_out_channel oc in
      Format.fprintf of_fmt "@[%a@]%!" f x)

module Option = struct
  include Stdlib.Option

  module O = struct
    let ( let+ ) r f = map f r
    let ( let* ) r f = bind r f
  end
end
