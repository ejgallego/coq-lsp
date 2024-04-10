Definition map_union_weak `{β A, Insert K A (M A), ∀ A, Empty (M A), ∀ A, 
   Lookup K A (M A),
    ∀ A, FinMapToList K A (M A)} {A} (m1 m2 : M A) :=
  map_imap (λ l v, Some (default v (m1 !! l))) m2.

Section theorems.

Lemma map_union_weak_insert {K A} `{Countable K} (m1 m2 : gmap K A) (i : K) (x : A):
    map_union_weak (<[i := x]>m1) m2 = alter (λ _, x) i (map_union_weak m1 m2).
