General tests for the Flèche Compiler

Describe the project
  $ export FCC_TEST=true
  $ fcc --root proj1
  [message] Configuration loaded from Command-line arguments
   - coqlib is at: [TEST_PATH]
     + coqcorelib is at: [TEST_PATH]
   - Modules [Coq.Init.Prelude] will be loaded by default
   - 2 Coq path directory bindings in scope; 22 Coq plugin directory bindings in scope
   - ocamlpath wasn't overriden
     + findlib config: [TEST_PATH]
     + findlib default location: [TEST_PATH]

Compile a single file
  $ fcc --root proj1 proj1/a.v
  [message] Configuration loaded from Command-line arguments
   - coqlib is at: [TEST_PATH]
     + coqcorelib is at: [TEST_PATH]
   - Modules [Coq.Init.Prelude] will be loaded by default
   - 2 Coq path directory bindings in scope; 22 Coq plugin directory bindings in scope
   - ocamlpath wasn't overriden
     + findlib config: [TEST_PATH]
     + findlib default location: [TEST_PATH]
  [message] compiling file proj1/a.v
  
  $ ls proj1
  a.diags
  a.v
  a.vo
  b.v

Compile a single file, silent
  $ fcc --display=quiet --root proj1 proj1/a.v

Compile a dependent file
  $ fcc --root proj1 proj1/b.v
  [message] Configuration loaded from Command-line arguments
   - coqlib is at: [TEST_PATH]
     + coqcorelib is at: [TEST_PATH]
   - Modules [Coq.Init.Prelude] will be loaded by default
   - 2 Coq path directory bindings in scope; 22 Coq plugin directory bindings in scope
   - ocamlpath wasn't overriden
     + findlib config: [TEST_PATH]
     + findlib default location: [TEST_PATH]
  [message] compiling file proj1/b.v
  
  $ ls proj1
  a.diags
  a.v
  a.vo
  b.diags
  b.v
  b.vo

Compile both files
  $ rm proj1/*.vo
  $ fcc --root proj1 proj1/a.v proj1/b.v
  [message] Configuration loaded from Command-line arguments
   - coqlib is at: [TEST_PATH]
     + coqcorelib is at: [TEST_PATH]
   - Modules [Coq.Init.Prelude] will be loaded by default
   - 2 Coq path directory bindings in scope; 22 Coq plugin directory bindings in scope
   - ocamlpath wasn't overriden
     + findlib config: [TEST_PATH]
     + findlib default location: [TEST_PATH]
  [message] compiling file proj1/a.v
  
  [message] compiling file proj1/b.v
  
  $ ls proj1
  a.diags
  a.v
  a.vo
  b.diags
  b.v
  b.vo

Compile a dependent file without the dep being built
  $ rm proj1/*.vo
  $ fcc --root proj1 proj1/b.v
  [message] Configuration loaded from Command-line arguments
   - coqlib is at: [TEST_PATH]
     + coqcorelib is at: [TEST_PATH]
   - Modules [Coq.Init.Prelude] will be loaded by default
   - 2 Coq path directory bindings in scope; 22 Coq plugin directory bindings in scope
   - ocamlpath wasn't overriden
     + findlib config: [TEST_PATH]
     + findlib default location: [TEST_PATH]
  [message] compiling file proj1/b.v
  
  $ ls proj1
  a.diags
  a.v
  b.diags
  b.v
  b.vo
  $ cat proj1/a.diags
  {
    "range": {
      "start": { "line": 0, "character": 0 },
      "end": { "line": 0, "character": 19 }
    },
    "severity": 4,
    "message": "aa is defined"
  }
  {
    "range": {
      "start": { "line": 6, "character": 0 },
      "end": { "line": 6, "character": 4 }
    },
    "severity": 4,
    "message": "foo is defined"
  }
  $ cat proj1/b.diags
  {
    "range": {
      "start": { "line": 0, "character": 0 },
      "end": { "line": 0, "character": 10 }
    },
    "severity": 1,
    "message": "Cannot find a physical path bound to logical path a."
  }
  {
    "range": {
      "start": { "line": 1, "character": 17 },
      "end": { "line": 1, "character": 21 }
    },
    "severity": 1,
    "message": "The reference a.aa was not found in the current environment."
  }

Use two workspaces
  $ rm proj1/*.vo
  $ fcc --root proj1 --root proj2 proj1/a.v proj2/b.v
  [message] Configuration loaded from Command-line arguments
   - coqlib is at: [TEST_PATH]
     + coqcorelib is at: [TEST_PATH]
   - Modules [Coq.Init.Prelude] will be loaded by default
   - 2 Coq path directory bindings in scope; 22 Coq plugin directory bindings in scope
   - ocamlpath wasn't overriden
     + findlib config: [TEST_PATH]
     + findlib default location: [TEST_PATH]
  [message] Configuration loaded from Command-line arguments
   - coqlib is at: [TEST_PATH]
     + coqcorelib is at: [TEST_PATH]
   - Modules [Coq.Init.Prelude] will be loaded by default
   - 2 Coq path directory bindings in scope; 22 Coq plugin directory bindings in scope
   - ocamlpath wasn't overriden
     + findlib config: [TEST_PATH]
     + findlib default location: [TEST_PATH]
  [message] compiling file proj1/a.v
  
  [message] compiling file proj2/b.v
  
  fcc: internal error, uncaught exception:
       Sys_error("proj2/b.v: No such file or directory")
       
  [125]

Load the example plugin
  $ fcc --plugin=coq-lsp.plugin.example --root proj1 proj1/a.v
  [message] Configuration loaded from Command-line arguments
   - coqlib is at: [TEST_PATH]
     + coqcorelib is at: [TEST_PATH]
   - Modules [Coq.Init.Prelude] will be loaded by default
   - 2 Coq path directory bindings in scope; 22 Coq plugin directory bindings in scope
   - ocamlpath wasn't overriden
     + findlib config: [TEST_PATH]
     + findlib default location: [TEST_PATH]
  [message] compiling file proj1/a.v
  
  [example plugin] file checking for proj1/a.v was completed

Load the astdump plugin
  $ fcc --plugin=coq-lsp.plugin.astdump --root proj1 proj1/a.v
  [message] Configuration loaded from Command-line arguments
   - coqlib is at: [TEST_PATH]
     + coqlib is at: [TEST_PATH]
   - Modules [Coq.Init.Prelude] will be loaded by default
   - 2 Coq path directory bindings in scope; 22 Coq plugin directory bindings in scope
   - ocamlpath wasn't overriden
     + coqlib is at: [TEST_PATH]
     + coqlib is at: [TEST_PATH]
  [message] compiling file proj1/a.v
  
  [ast plugin] dumping ast for proj1/a.v ...
  [ast plugin] dumping ast for proj1/a.v was completed!
  $ md5sum proj1/a.v.json.astdump
  3b0cdd303aac62d35ba0c765b4d1c373  proj1/a.v.json.astdump
  $ md5sum proj1/a.v.sexp.astdump
  af5864db39cb58fdc402f8d7d639b5d0  proj1/a.v.sexp.astdump
