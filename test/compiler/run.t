General tests for the Flèche Compiler

Describe the project
  $ fcc --root proj1
  [message] Configuration loaded from Command-line arguments
   - coqlib is at: [TEST_PATH]
   - Modules [Coq.Init.Prelude] will be loaded by default
   - 2 Coq path directory bindings in scope; 22 Coq plugin directory bindings in scope

Compile a single file
  $ fcc --root proj1 proj1/a.v
  [message] Configuration loaded from Command-line arguments
   - coqlib is at: [TEST_PATH]
   - Modules [Coq.Init.Prelude] will be loaded by default
   - 2 Coq path directory bindings in scope; 22 Coq plugin directory bindings in scope
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
   - Modules [Coq.Init.Prelude] will be loaded by default
   - 2 Coq path directory bindings in scope; 22 Coq plugin directory bindings in scope
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
   - Modules [Coq.Init.Prelude] will be loaded by default
   - 2 Coq path directory bindings in scope; 22 Coq plugin directory bindings in scope
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
   - Modules [Coq.Init.Prelude] will be loaded by default
   - 2 Coq path directory bindings in scope; 22 Coq plugin directory bindings in scope
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
   - Modules [Coq.Init.Prelude] will be loaded by default
   - 2 Coq path directory bindings in scope; 22 Coq plugin directory bindings in scope
  [message] Configuration loaded from Command-line arguments
   - coqlib is at: [TEST_PATH]
   - Modules [Coq.Init.Prelude] will be loaded by default
   - 2 Coq path directory bindings in scope; 22 Coq plugin directory bindings in scope
  [message] compiling file proj1/a.v
  
  [message] compiling file proj2/b.v
  
  fcc: internal error, uncaught exception:
       Sys_error("proj2/b.v: No such file or directory")
       
  [125]

Load the example plugin
  $ fcc --plugin=coq-lsp.plugin.example --root proj1 proj1/a.v
  [message] Configuration loaded from Command-line arguments
   - coqlib is at: [TEST_PATH]
   - Modules [Coq.Init.Prelude] will be loaded by default
   - 2 Coq path directory bindings in scope; 22 Coq plugin directory bindings in scope
  [message] compiling file proj1/a.v
  
  [example plugin] file checking for proj1/a.v was completed
