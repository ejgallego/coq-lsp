Degenerate performance case for the fcc compiler
  $ export FCC_TEST=true

Generate the test file (example by G. Gilbert)

  $ for i in $(seq 1 10000); do printf 'Lemma foo%s : nat.\nProof. exact 0. Qed.\n\n' $i; done > test.v

We now compile the challenging file:
  $ fcc --root . ./test.v
  [message] Configuration loaded from Command-line arguments
   - findlib: [TEST_PATH]
     + findlib config: [TEST_PATH]
     + findlib default location: [TEST_PATH]
   - coqlib is at: [TEST_PATH]
     + 2 Coq path directory bindings in scope
     + Modules [Coq.Init.Prelude] will be loaded by default
  [message] compiling file ./test.v
