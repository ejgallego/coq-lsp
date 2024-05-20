(* Copyright (C) 2002, 2003 Yamagata Yoriyuki. *)

(* This library is free software; you can redistribute it and/or *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2 of *)
(* the License, or (at your option) any later version. *)

(* As a special exception to the GNU Library General Public License, you *)
(* may link, statically or dynamically, a "work that uses this library" *)
(* with a publicly distributed version of this library to produce an *)
(* executable file containing portions of this library, and distribute *)
(* that executable file under terms of your choice, without any of the *)
(* additional requirements listed in clause 6 of the GNU Library General *)
(* Public License. By "a publicly distributed version of this library", *)
(* we mean either the unmodified Library as distributed by the authors, *)
(* or a modified version of this library that is distributed under the *)
(* conditions defined in clause 3 of the GNU Library General Public *)
(* License. This exception does not however invalidate any other reasons *)
(* why the executable file might be covered by the GNU Library General *)
(* Public License . *)

(* This library is distributed in the hope that it will be useful, *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU *)
(* Lesser General Public License for more details. *)

(* You should have received a copy of the GNU Lesser General Public *)
(* License along with this library; if not, write to the Free Software *)
(* Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 *)
(* USA *)

(* EJGA: Taken from Camomille, but note what I wrote below *)

(* utf8 utils, both Coq and Camomile have similar implementations, at some point
   we should remove this but for now we keep it internal. For now we use the
   Camomille functions *)

(** Unicode terminology refresher:
    - character, code point: The real unicode character
    - byte or 16bit offset / code unit: The encoded version *)

type utf8_string = string
type char = int
type utf8_index = int
type utf16_index = int

(** To unicode chars *)

(** Byte index to character position [also called a codepoint], line is enconded
    in UTF-8 *)
val char_of_utf8_offset : line:utf8_string -> offset:utf8_index -> char option

(** Get the unicode position of a code point indexed in UTF-16 code units in a
    utf-8 encoded utf8_string. Returns the position of the last character if the
    utf-16 position was out of bounds. *)
val char_of_utf16_offset : line:utf8_string -> offset:utf16_index -> char

(** To UTF-8 offsets *)

(** UTF-8 Char to byte index position; line is enconded in UTF-8 *)
val utf8_offset_of_char : line:utf8_string -> char:char -> utf8_index option

(** Get the byte position of a code point indexed in UTF-16 code units in a
    UTF-8 encoded utf8_string. Returns the position of the last character if the
    UTF-16 position was out of bounds. *)
val utf8_offset_of_utf16_offset :
  line:utf8_string -> offset:utf16_index -> utf8_index

(** To UTF-16 offsets *)

(** Get the utf16 position of a code point indexed in unicode code points in a
    UTF-8 encoded utf8_string. The position must be in bounds. *)
val utf16_offset_of_char : line:utf8_string -> char:int -> utf16_index

(** Number of characters in th utf-8-encoded utf8_string *)
val length : utf8_string -> char
