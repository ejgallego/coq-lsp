Require Coq.extraction.Extraction.

Extraction Language Haskell.

Extraction Implicit pred [1].

Axiom Y : Set -> Set -> Set.
Extract Constant Y "'a" "'b" => " 'a * 'b ".
