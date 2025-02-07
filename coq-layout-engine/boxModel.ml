(************************************************************************)
(* coq-layout-engine                                                    *)
(* Copyright 2021 Inria                                                 *)
(* Written by Emilio J. Gallego Arias                                   *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

type abs_kind =
  | Prod
  | Lam

module Id = struct
  type 'a t =
    { relative : string
    ; absolute : string option
    ; typ : 'a option
    }
end

module Variable = struct
  type 'a t =
    { name : string
    ; typ : 'a
    }
end

module Binder = struct
  type 'a t =
    { namel : string list
    ; typ : 'a
    }

  let map ~f b = { b with typ = f b.typ }
end

(** Output Layout Box model, designed to be embedded in DOM almost directly, and
    to replace Pp.t *)
type t =
  | Variable of t Variable.t  (** Variable *)
  | Constant of string  (** Constant (lexical) *)
  | Identifier of t Id.t  (** Identifier *)
  | Sort of string list  (** Sort *)
  | App of
      { fn : t
      ; impl : t list
      ; argl : t list
      }  (** Application box *)
  | Cast of t option * t  (** Cast box *)
  | Abs of
      { kind : abs_kind
      ; binderl : t Binder.t list
      ; v : t
      }  (** Abstraction *)
  (* XXX Use binder.t *)
  | Let of
      { lhs : t
      ; rhs : t
      ; typ : t option
      ; v : t
      }  (** Let *)
  | Notation of
      { key : string
      ; args : t list
      ; pretty : t list
      ; raw : t
      }  (** Notation *)
  | Fixpoint of t * t

(** Renderer *)
module H = Tyxml.Html

module LaTeX = struct

  type t =
    | Token of string
    | Macro of string * t list
    | List of t list

  let macro s = Macro(s, [])
end

module Render = struct
  let xxx kind = H.txt ("uninplemented: " ^ kind)
  let _class c = [ H.a_class [ c ] ]

  let span ?(extra = []) c e =
    let a = _class c in
    H.span ~a (extra @ e)

  let id_to_html id = span "identifier" [ H.txt id ]

  let binder_to_html ({ Binder.namel; typ } : _ Binder.t) : _ H.elt =
    let namel = List.map H.txt namel in
    span "binder" [ span "namel" namel; span "btype" [ typ ] ]

  let rec to_html (b : t) : _ H.elt =
    match b with
    | Variable { name; typ } ->
      let name = span "name" [ id_to_html name ] in
      let typ = span "type" [ to_html typ ] in
      span "variable" [ name; typ ]
    | Constant c -> span "constant" [ H.txt c ]
    | Identifier { relative; absolute; typ } ->
      span "reference"
      @@ [ span "relative" [ H.txt relative ] ]
      @ Option.cata (fun a -> [ span "absolute" [ H.txt a ] ]) [] absolute
      @ Option.cata (fun typ -> [ span "type" [ to_html typ ] ]) [] typ
    | Cast (_c, t) -> span "cast" @@ [ to_html t ]
    | Sort e -> span "sort" @@ List.map H.txt e
    | App { fn; impl = _; argl } ->
      let fn = to_html fn in
      let argl = List.map to_html argl in
      span "app" [ H.txt "("; fn; span "args" argl; H.txt ")" ]
    | Abs { kind; binderl; v } ->
      let head, delim =
        match kind with
        | Prod -> ("forall", ",")
        | Lam -> ("fun", "=>")
      in
      let binderl = List.map (Binder.map ~f:to_html) binderl in
      let binderl = List.map binder_to_html binderl in
      let v = to_html v in
      span "abs" [ H.txt head; span "binderl" binderl; H.txt delim; v ]
    | Let _ -> xxx "let"
    | Notation { key; args; pretty; raw } ->
      let t_h = span "arguments" (List.map to_html args) in
      let pretty_h = List.map to_html pretty in
      span "notation"
        [ span "key" [ H.txt key ]
        ; t_h
        ; span "pretty" pretty_h
        ; span "raw" [ to_html raw ]
        ]
    | Fixpoint (_, _) -> xxx "fixpoint"

  module LaTeX = struct

    let binder_to_latex : _ Binder.t -> LaTeX.t =
      function { Binder.namel; _ } ->
        LaTeX.List([Token "("; LaTeX.List(List.map (fun x -> LaTeX.Token x) namel); Token")"])
    
    let rec to_latex : t -> LaTeX.t =
      let open LaTeX in 
      function
       | Variable {name; _ } -> Token name
       | Constant c -> Token c
       | Identifier {relative ; absolute = _ ; _ } -> Token relative
       | Sort e -> List (List.map (fun e -> Token e) e)
       | App {fn; impl= _; argl} -> List(to_latex fn :: (List.map to_latex argl))
       | Cast (_c, t) -> to_latex t
       | Abs {kind; binderl; v} ->
         (* let head, delim = *)
         let binderl = List.map (Binder.map ~f:to_latex) binderl in
         let binderl = List.map binder_to_latex binderl in         
         (match kind with
         | Prod -> List( (macro "prod") :: to_latex v :: binderl)
         | Lam ->  List( (macro "lambda") :: to_latex v :: binderl))
       | Let {lhs; rhs; typ =_; v} ->
         List([Token "let";
               to_latex lhs;
               Token ":=";
               to_latex rhs;
               Token "in";
               to_latex v])
       | Notation _ -> Token ""
       | Fixpoint (f1, f2) ->
         List([Token "fix"; to_latex f1; to_latex f2 ])
  end
  let to_latex = LaTeX.to_latex
end
