# coq-lsp 0.1.1: Location
-------------------------

 - Don't crash if the log file can't be created (@ejgallego, #87)
 - Use LSP functions for client-side logging (@ejgallego, #87)
 - Log `_CoqProject` detection settings to client window (@ejgallego, #88)
 - Use plugin include paths from `_CoqProject` (@ejgallego, #88)
 - Support OCaml >= 4.12 (@ejgallego, #93)
 - Optimize the number of diagnostics sent in eager mode (@ejgallego, #104)
 - Improved syntax highlighting on VSCode client (@artagnon, #105)
 - Resume document checking from the point it was interrupted
   (@ejgallego, #95, #99)
 - Don't convert Coq "Info" messages such as "Foo is defined" to
   feedback by default; users willing to see them can set the
   corresponding option (@ejgallego, #113)
 - Send `$/coq/fileProgress` progress notifications from server,
   similarly to what Lean does; display them in Code's right gutter
   (@ejgallego, #106, fixes #54)
 - Show goals on click by default, allow users to configure the
   behavior to follow cursor in different ways (@ejgallego, #116,
   fixes #89)
 - Show file position in goal buffer, use collapsible elements for
   goal list (@ejgallego, #115, fixes #109)
 - Resume checking from common prefix on document update (@ejgallego,
   #111, fixes #110)

# coq-lsp 0.1.0: Memory
-----------------------

 - Location-aware cache for incremental Coq interpretation (@ejgallego)
 - Smart, structure-aware error recovery (@ejgallego)
 - Configure flags reading _CoqProject file (@artagnon, #3)
 - Interruption support (@ejgallego , @Alizter, #27, #32, #34)
 - Markdown support (@ejgallego, #62)
 - Goal display (@ejgallego @corwin-of-amber, #69)
 - User-side configuration (@ejgallego, #67)
 - Allow to configure before/after goal display (@ejgallego, #78)
 - Allow requests to interrupt checking (@ejgallego, #76)

# coq-lsp 0.0.0.1
-----------------

 - Bootstrap from lambdapi-lsp server (@ejgallego)
