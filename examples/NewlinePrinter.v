Require Import Ascii String List.

Definition nl := (String (ascii_of_nat 10) "")%string.

Import ListNotations.
Local Open Scope string.

Definition paragraph := ["These"; "Should"; "Be"; "On"; "New"; "Lines"].

Definition para_string := String.concat nl paragraph.

Axiom P : string -> Prop.

Goal P para_string.
cbv.
