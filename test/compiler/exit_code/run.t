Test for exit code of the compiler and `max_errors`

Describe the environment:
  $ export FCC_TEST=true
  $ export FCC_ROOT=./
  $ fcc --root $FCC_ROOT
  [message] Configuration loaded from ./_CoqProject
   - coqlib is at: [TEST_PATH]
     + coqcorelib is at: [TEST_PATH]
   - Modules [Coq.Init.Prelude] will be loaded by default
   - 3 Coq path directory bindings in scope; 22 Coq plugin directory bindings in scope
   - ocamlpath wasn't overriden
     + findlib config: [TEST_PATH]
     + findlib default location: [TEST_PATH]

Compile normally, even with errors, we exit 0:
  $ fcc --display=quiet --no_vo --root $FCC_ROOT Demo.v
  $ echo $?
  0
  $ cat Demo.diags
  {
    "range": {
      "start": { "line": 11, "character": 8 },
      "end": { "line": 11, "character": 15 }
    },
    "severity": 1,
    "message": "add_0_r already exists."
  }
  {
    "range": {
      "start": { "line": 13, "character": 0 },
      "end": { "line": 13, "character": 4 }
    },
    "severity": 1,
    "message": "Command not supported (No proof-editing in progress)."
  }

Compile normally, with more errors than we have, we exit 0:
  $ fcc --display=quiet --no_vo --max_errors=2 --root $FCC_ROOT Demo.v

Compile normally, with more error than we allow, we exit 1:
  $ fcc --display=quiet --no_vo --max_errors=1 --root $FCC_ROOT Demo.v
  [1]

