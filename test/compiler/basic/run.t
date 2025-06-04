General tests for the Flèche Compiler

Describe the project
  $ export FCC_TEST=true
  $ fcc --root proj1
  [message] Configuration loaded from Command-line arguments
   - findlib: [TEST_PATH]
     + findlib config: [TEST_PATH]
     + findlib default location: [TEST_PATH]
   - coqlib is at: [TEST_PATH]
     + 2 Coq path directory bindings in scope
     + Modules [Coq.Init.Prelude] will be loaded by default

Compile a single file, don't generate a `.vo` file:
  $ fcc --no_vo --root proj1 proj1/a.v
  [message] Configuration loaded from Command-line arguments
   - findlib: [TEST_PATH]
     + findlib config: [TEST_PATH]
     + findlib default location: [TEST_PATH]
   - coqlib is at: [TEST_PATH]
     + 2 Coq path directory bindings in scope
     + Modules [Coq.Init.Prelude] will be loaded by default
  [message] compiling file proj1/a.v

  $ ls proj1
  a.diags
  a.v
  b.v

Compile a single file, generate a .vo file
  $ fcc --root proj1 proj1/a.v
  [message] Configuration loaded from Command-line arguments
   - findlib: [TEST_PATH]
     + findlib config: [TEST_PATH]
     + findlib default location: [TEST_PATH]
   - coqlib is at: [TEST_PATH]
     + 2 Coq path directory bindings in scope
     + Modules [Coq.Init.Prelude] will be loaded by default
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
   - findlib: [TEST_PATH]
     + findlib config: [TEST_PATH]
     + findlib default location: [TEST_PATH]
   - coqlib is at: [TEST_PATH]
     + 2 Coq path directory bindings in scope
     + Modules [Coq.Init.Prelude] will be loaded by default
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
   - findlib: [TEST_PATH]
     + findlib config: [TEST_PATH]
     + findlib default location: [TEST_PATH]
   - coqlib is at: [TEST_PATH]
     + 2 Coq path directory bindings in scope
     + Modules [Coq.Init.Prelude] will be loaded by default
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
   - findlib: [TEST_PATH]
     + findlib config: [TEST_PATH]
     + findlib default location: [TEST_PATH]
   - coqlib is at: [TEST_PATH]
     + 2 Coq path directory bindings in scope
     + Modules [Coq.Init.Prelude] will be loaded by default
  [message] compiling file proj1/b.v
  $ ls proj1
  a.diags
  a.v
  b.diags
  b.v
  b.vo
  $ cat proj1/a.diags
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

Compile a file with all messages:
  $ rm -f proj1/a.{diags,vo}
  $ fcc --root proj1 --diags_level=1 proj1/a.v
  [message] Configuration loaded from Command-line arguments
   - findlib: [TEST_PATH]
     + findlib config: [TEST_PATH]
     + findlib default location: [TEST_PATH]
   - coqlib is at: [TEST_PATH]
     + 2 Coq path directory bindings in scope
     + Modules [Coq.Init.Prelude] will be loaded by default
  [message] compiling file proj1/a.v
  $ cat proj1/a.diags
  $ fcc --root proj1 --diags_level=2 proj1/a.v
  [message] Configuration loaded from Command-line arguments
   - findlib: [TEST_PATH]
     + findlib config: [TEST_PATH]
     + findlib default location: [TEST_PATH]
   - coqlib is at: [TEST_PATH]
     + 2 Coq path directory bindings in scope
     + Modules [Coq.Init.Prelude] will be loaded by default
  [message] compiling file proj1/a.v
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

Use two workspaces
  $ rm proj1/*.vo
  $ fcc --root proj1 --root proj2 proj1/a.v proj2/b.v
  [message] Configuration loaded from Command-line arguments
   - findlib: [TEST_PATH]
     + findlib config: [TEST_PATH]
     + findlib default location: [TEST_PATH]
   - coqlib is at: [TEST_PATH]
     + 2 Coq path directory bindings in scope
     + Modules [Coq.Init.Prelude] will be loaded by default
  [message] Configuration loaded from Command-line arguments
   - findlib: [TEST_PATH]
     + findlib config: [TEST_PATH]
     + findlib default location: [TEST_PATH]
   - coqlib is at: [TEST_PATH]
     + 2 Coq path directory bindings in scope
     + Modules [Coq.Init.Prelude] will be loaded by default
  [message] compiling file proj1/a.v
  [message] compiling file proj2/b.v
  fcc: internal error, uncaught exception:
       Sys_error("proj2/b.v: No such file or directory")
       
  [125]

Load the example plugin
  $ fcc --plugin=coq-lsp.plugin.example --root proj1 proj1/a.v
  [message] Configuration loaded from Command-line arguments
   - findlib: [TEST_PATH]
     + findlib config: [TEST_PATH]
     + findlib default location: [TEST_PATH]
   - coqlib is at: [TEST_PATH]
     + 2 Coq path directory bindings in scope
     + Modules [Coq.Init.Prelude] will be loaded by default
  [message] compiling file proj1/a.v
  [message] [example plugin] file checking for proj1/a.v was completed

Load the astdump plugin
  $ fcc --plugin=coq-lsp.plugin.astdump --root proj1 proj1/a.v
  [message] Configuration loaded from Command-line arguments
   - findlib: [TEST_PATH]
     + findlib config: [TEST_PATH]
     + findlib default location: [TEST_PATH]
   - coqlib is at: [TEST_PATH]
     + 2 Coq path directory bindings in scope
     + Modules [Coq.Init.Prelude] will be loaded by default
  [message] compiling file proj1/a.v
  [message] [ast plugin] dumping ast for proj1/a.v ...
  [message] [ast plugin] dumping ast for proj1/a.v was completed!

EJGA: I'd be nice to check the checksum of files here, however
`md5sum` is not avilable on all of our CI platforms yet. `ls -l`
output is also not fully portable, so we settle for this check for now.

Another way to test this would be to have an `undump` plugin, so we
de-serialize the document back and check.

  $ ls proj1/a.v.jsonl.astdump proj1/a.v.sexpl.astdump
  proj1/a.v.jsonl.astdump
  proj1/a.v.sexpl.astdump

We do the same for the goaldump plugin:
  $ fcc --plugin=coq-lsp.plugin.goaldump --root proj1 proj1/a.v
  [message] Configuration loaded from Command-line arguments
   - findlib: [TEST_PATH]
     + findlib config: [TEST_PATH]
     + findlib default location: [TEST_PATH]
   - coqlib is at: [TEST_PATH]
     + 2 Coq path directory bindings in scope
     + Modules [Coq.Init.Prelude] will be loaded by default
  [message] compiling file proj1/a.v
  [message] [goaldump plugin] dumping goals for proj1/a.v ...
  [message] [goaldump plugin] dumping ast for proj1/a.v was completed!
  $ ls proj1/a.v.json.goaldump
  proj1/a.v.json.goaldump
