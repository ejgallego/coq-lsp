Degenerate performance case for the fcc compiler
  $ export FCC_TEST=true

Generate the test file (example by G. Gilbert)

  $ for i in $(seq 1 10000); do printf 'Lemma foo%s : nat.\nProof. exact 0. Qed.\n\n' $i; done > test.v

We now compile the challenging file:
  $ fcc --root . ./test.v
  [message] Configuration loaded from Command-line arguments
<<<<<<< HEAD
   - coqlib is at: [TEST_PATH]
     + coqcorelib is at: [TEST_PATH]
   - Modules [Coq.Init.Prelude] will be loaded by default
   - 2 Coq path directory bindings in scope; 24 Coq plugin directory bindings in scope
   - ocamlpath added paths: []
=======
   - findlib: [TEST_PATH]
>>>>>>> main
     + findlib config: [TEST_PATH]
     + findlib default location: [TEST_PATH]
   - coqlib is at: [TEST_PATH]
     + 2 Coq path directory bindings in scope
     + Modules [Corelib.Init.Prelude] will be loaded by default
  [message] compiling file ./test.v
