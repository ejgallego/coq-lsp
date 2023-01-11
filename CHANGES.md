# coq-lsp 0.1.5: Form
---------------------

 - Fix a bug when trying to complete in an empty file (@ejgallego,
   #270)
 - Fix a bug with the position reported by the `$/coq/fileProgress`
   notification
 - Fix messages panel rendering after the port to React (@ejgallego,
   #272)
 - Fix non-compliance with LSP range type due to extra `offset` field
   (@ejgallego, #271)
 - The goal display now numbers goals starting with 1 instead of 0
   (@artagnon, #277, report by Hugo Herbelin)
 - Markdown Coq code blocks now must specify "coq" as a language
   (@ejgallego, #280)
 - Server is now more strict w.r.t. what URIs it will accept for
   documents, see protocol documentation (@ejgallego, #286, reported
   by Alex Sanchez-Stern)
 - Hypothesis with bodies are now correctly displayed (@ejgallego,
   #296, fixes #293, report by Ali Caglayan)
 - `coq-lsp` incorrectly required the optional `rootPath`
   initialization parameter, moreover it ignored `rootUri` if present
   which goes against the LSP spec (@ejgallego, #295, report by Alex
   Sanchez-Stern)
 - `coq-lsp` will now reject opening multiple files when the
   underlying Coq version is buggy (@ejgallego, fixes #275, fixes
   #281)
 - Fix bug when parsing client option for unicode completion
   (@ejgallego #301)
 - Support unicode characters in filenames (@artagnon, #302)
 - Stop checking documents after a maximum number of errors,
   user-configurable (by default 150) (@ejgallego, #303)
 - Coq Markdown files (.mv extension) are now highlighted properly
   using both Coq and Markdown syntax rules (@4ever2, #307)
 - Goal view now supports find (@Alizter, #309, closes #305)
 - coq-lsp now understands a basic version of Coq Waterproof files
   (.wpn) Note that we don't associate to them by default, as to allow
   the waterproof extension to take over the files (@ejgallego, #306)
 - URI validation is now more strict, and some further bugs should be
   solved; note still this can be an issue on some client settings
   (@ejgallego, #313, fixes #187)
 - Display Coq info and debug messages in info panel (@ejgallego,
   #314, fixes #308)
 - Goal display handles background goals better, showing preview,
   goals stack, and focusing information (@ejgallego, #290, fixes
   #288, based on jsCoq code by Shachar Itzhaky)
 - Warnings are now printed in the info view messages panel
   (@ejgallego, #315, fixes #195)
 - Info protocol messages now have location and level
   (@ejgallego, #315)
 - Warnings are not printed in the info view messages panel
   (@ejgallego, #, fixes #195)
 - Improved `documentSymbol` return type for newer `DocumentSymbol[]`
   hierarchical symbol support. This means that sections and modules
   will now be properly represented, as well as constructors for
   inductive types, projections for records, etc...  (@ejgallego,
   #174, fixes #121, #122)

# coq-lsp 0.1.4: View
---------------------

 - Support for OCaml 4.11 (@ejgallego, #184)
 - The keybinding alt+enter in VSCode is now correctly scoped to be
   only active on Coq files (@artagnon, #188)
 - Support Unicode files (@ejgallego, #200, fixes #193, fixes #197)
 - The info view is now script enabled and does client-side
   rendering. It is also now bundled with esbuild as part of the build
   process (@artagnon, @ejgallego, #171)
 - The no-op `--std` argument to the `coq-lsp` binary has been
   removed, beware of your setup in the extension settings
   (@ejgallego, #208)
 - Settings for the VSCode extension are now categorized (@Alizter, #212)
 - `GoalAnswer`s now include the proof "stack" and better hypothesis
   information, changes are compatible with 0.1.3 `GoalAnswer` version
   (@ejgallego, #237)
 - Focus is now preserved when the info view pops up (@artagnon, #242,
   fixes #224)
 - In `_CoqProject`, `-impredicative-set` is now parsed correctly
   (@artagnon, #241)
 - InfoView is not written in React (@ejgallego, #223)
 - `debug` option in the client / protocol that will enable Coq's backtraces
   (@Alizter, @ejgallego, #217, #248)
 - Full document stats are now correctly computed on checking
   resumption, still cached sentences will display the cached timing
   tho (@ejgallego, #257)
 - Set Coq library name correctly from URI, note this makes the server
   to accept less URIs (@ejgallego, #260)
 - `_CoqProject` file is now detected using LSP client `rootPath`
   (@ejgallego, #261)
 - You can press `\` to trigger Unicode completion by the server. This
   behavior is configurable, with "off", "regular", and "extended"
   settings (@artagnon, @Alizter, ejgallego, #219).

# coq-lsp 0.1.3: Event
----------------------

 - Much improved handling of Coq fatal errors, the server is now
   hardened against them (@ejgallego, #155, #157, #160, fixes #91)
 - `coq-lsp` now follows the LSP specification regarding
   initialization strictly (@ejgallego, #168)
 - New setting for goals to be updated when the selection changes due
   to a command; this makes VsCodeVim cursor tracking work; thanks to
   Cactus (Anton) Golov for detailed bug reporting and testing
   (@ejgallego, @jesyspa, #170, fixes #163)
 - `coq-lsp` will now warn the user when two files have been opened
   simultaneously and the parser may go into a broken state :/
   (@ejgallego, #169)
 - Implement request postponement and cancellation. Thus
   `documentSymbols` will now be postponed until the document is
   ready, (@ejgallego, #141, #146, fixes #124)
 - Protocol and VS Code interfaces now support shelved and given_up
   goals (@ejgallego, #175)
 - Allow to postpone requests to wait for data to become available on
   document points; this is implemented to provide a nicer "show goals
   while I type" experience. Client default has been changed to "show
   goals on mouse, click, typing, and cursor movement) (@ejgallego,
   #177, #179)
 - Store stats per document (@ejgallego, #180, fixes #173)

# coq-lsp 0.1.2: Message
------------------------

 - Send an error to the client if the client and server versions don't
   match (@ejgallego, #126)
 - Parse options -noinit, -indices-matter, and -impredicative-set from
   `_CoqProject` (@artagnon, @ejgallego, #140, #150)
 - Log file `log-lsp.txt` has been removed in favor of `coq-lsp.trace.server`
   (@artagnon, @ejgallego, #130, #148)
 - Added --bt flag to print a backtrace on error (@Alizter, #147)
 - A detailed view of Coq errors is now displayed in the info panel
   (@ejgallego, #128)
 - Coq "Notice" messages, such as the ones generated by `About` or
   `Search` are not shown anymore as diagnostics. Instead, they will
   be shown on the side panel when clicking on the corresponding
   command. The `show_notices_as_diagnostics` option allows to restore
   old behavior (@ejgallego, #128, fixes #125)
 - Print some more info about Coq workspace configuration (@ejgallego, #151)
 - Admit failed `Qed` by default; allow users to configure it
   (@ejgallego, #118, fixes #90)

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
 - Only serve goals, hover, and symbols requests when the document
   has been sufficiently processed (@ejgallego, #120, fixes #100)

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
