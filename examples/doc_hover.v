From Coq Require Import List.
Import ListNotations.

(* asdf *)
Definition hello := 3.

(** `my_map` a reimplementation of `map`

 - this is cool
 - really
 
 a source code example. 
 
 ```coq
 Definition my_map bar := 3.
 ```
 Pretty _nice_ :D
*)
Fixpoint my_map {A B} (f : A -> B) (l : list A) : list B :=
  match l with
    | [] => []
    | (x :: xs) => (f x :: my_map f xs)
  end.

(** I'm going to use `my_map` *)
Definition my_map_alias := @my_map.

About my_map_alias.
About hello.
