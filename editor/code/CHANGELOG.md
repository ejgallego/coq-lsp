# coq-lsp 0.2.2: To Virtual or not To Virtual
---------------------------------------------

 - [vscode] Expand selectors to include `vscode-vfs://` URIs used in
   `github.dev`, document limited virtual workspace support in
   `package.json` (@ejgallego, #849)

# coq-lsp 0.2.1: Click !
------------------------

 This release brings full Web Extension support for coq-lsp!

 You can now run Coq from your browser using https://vscode.dev or
 https://github.dev .

 Some other highlights is `codeAction` support (for Coq quick fixes),
 `Restart.` support, better API for our extension users, and many
 bugfixes and improvements, in particular for `hover`.

 The detailed list of server and client changes is below:

 - [workspace] [coq] Support _CoqProject arguments `-type-in-type` and
   `-allow-rewrite-rules` (for 8.20) (@ejgallego, #819)
 - [serlib] Fix Ltac2 AST piercing bug, add test case that should help
   in the future (@ejgallego, @jim-portegies, #821)
 - [fleche] [8.20] understand rewrite rules and symbols on document
   outline (@ejgallego, @Alizter, #825, fixes #824)
 - [fleche] [coq] support `Restart` meta command (@ejgallego,
   @Alizter, #828, fixes #827)
 - [fleche] [plugins] New plugin example `explain_errors`, that will
   print all errors on a file, with their goal context (@ejgallego,
   #829, thanks to @gmalecha for the idea, c.f. Coq issue 19601)
 - [fleche] Highlight the full first line of the document on
   initialization error (@ejgallego, #832)
 - [fleche] [jscoq] [js] Build worker version of `coq-lsp`. This
   provides a full working Coq enviroment in `vscode.dev`. The web
   worker version is build as an artifact on CI (@ejgallego
   @corwin-of-amber, #433)
 - [hover] Fix universe and level printing in hover (#839, fixes #835
   , @ejgallego , @Alizter)
 - [fleche] New immediate request serving mode. In this mode, requests
   are served with whatever document state we have. This is very
   useful when we are not in continuous mode, and we don't have a good
   reference as to what to build, for example in
   `documentSymbols`. The mode actually works pretty well in practice
   as often language requests will come after goals requests, so the
   info that is needed is at hand. It could also be tried to set the
   build target for immediate requests to the view hint, but we should
   see some motivation for that (@ejgallego, #841)
 - [lsp] [diagnostics] (! breaking change) change type of diagnostics
   extra data from list to named record (@ejgallego, #843)
 - [lsp] Implement support for `textDocument/codeAction`. For now, we
   support Coq's 8.21 `quickFix` data (@ejgallego, #840, #843, #845)
 - [petanque] Fix bug for detection of proof finished in deep stacks
   (@ejgallego, @gbdrt, #847)
 - [goals request] allow multiple Coq sentences in `command`. This is
   backwards compatible in the case that commands do not error, and
   users were sending just one command. (@ejgallego, #823, thanks to
   CoqPilot devs and G. Baudart for feedback)
 - [goals request] (! breaking) fail the request if the commands in
   `command` fail (@ejgallego, #823)

# coq-lsp 0.2.0: From Green to Blue
-----------------------------------

 - [fleche] Preserve view hint across document changes. With this
   change, we get local continuous checking mode when the view-port
   heuristic is enabled (@ejgallego, #748)
 - [vscode] Fix focus race when a Coq file is in column 2 (@ejgallego,
   #755, cc: #722, #725)
 - [hover] Show input howto for unicode characters on hover
   (@ejgallego, Léo Stefanesco, #756)
 - [lsp] [definition] Support for jump to definition across workspace
   files. The location information is obtained from `.glob` files, so
   it is often not perfect. (@ejgallego, #762, fixes #317)
 - [lsp] [hover] Show full name and provenance of identifiers
   (@ejgallego, #762)
 - [lsp] [definition] Try also to resolve and locate module imports
   (@ejgallego, #764)
 - [code] Don't start server on extension activation, unless an editor
   we own is active. We also auto-start the server if a document that
   we own is opened later (@ejgallego, #758, fixes #750)
 - [hover] New option `show_universes_on_hover` that will display
   universe data on hover (@ejgallego, @SkySkimmer, #666)
 - [hover] New plugin `unidiff` that will elaborate a summary of
   universe data a file, in particular regarding universes added at
   `Qed` time (@ejgallego, #773)
 - [fleche] Support meta-command `Abort All` (@ejgallego, #774, fixes
   #550)
 - [lsp] [petanque] Allow acces to `petanque` protocol from the lsp
   server (@ejgallego, #778)

  See server changelog for full server-side changes.

# coq-lsp 0.1.10: Hasta el 40 de Mayo _en effect_...
----------------------------------------------------

 - [code] Add `.v.tex` file extension to contributed language support
   (@ejgallego, #740).
 - [code] Don't show the panel on extension activation (@ejgallego,
   #741, fix #737)

# coq-lsp 0.1.9: Hasta el 40 de Mayo...
---------------------------------------

 - new configuration value `check_only_on_request` which will delay
   checking the document until a request has been made. This means
   users can now switch between continuous and on-demand modes. (#629,
   cc: #24, @ejgallego)
 - display the continous/on-request checking mode in the status bar,
   allow to change it by clicking on it (@ejgallego, #721)
 - new Coq Language Status Item that display server status, version,
   and memory use. We recommend the users to pin it.
 - new heatmap feature allowing timing data to be seen in the
   editor. use the `Coq LSP: Toggle heatmap` command. Colors and
   granularity are configurable, see settings (@Alizter, #686)
 - new VSCode commands to allow to move one sentence backwards /
   forward, this is particularly useful when combined with lazy
   checking mode (@ejgallego, #671, fixes #263, fixes #580)
 - VSCode commands `coq-lsp.sentenceNext` / `coq-lsp.sentencePrevious`
   are now bound by default to `Alt + N` / `Alt + P` keybindings
   (@ejgallego, #718)
 - new option `show_loc_info_on_hover` that will display parsing debug
   information on hover
 - fix activation bug that prevented extension activation for `.mv`
   files (@ejgallego @r3m0t, #598, cc #596, reported by Théo Zimmerman)
 - require VSCode >= 1.82 in package.json. (@ejgallego, #599,
   thanks to Théo Zimmerman for the report)
 - update progress indicator correctly on End Of File (@ejgallego,
   #605, fixes #445)
 - switch default of `goal_after_tactic` to `true` (@Alizter,
   @ejgallego, cc: #614)
 - error recovery: Recognize `Defined` and `Admitted` in lex recovery
   (@ejgallego, #616)
 - don't trigger the goals window in general markdown buffer
   (@ejgallego, #625, reported by Théo Zimmerman)
 - fix typo on package.json configuration section (@ejgallego, #645)
 - support for Coq 8.16 has been abandoned due to lack of dev
   resources (@ejgallego, #649)
 - new "Coq LSP: Free Memory" command to liberate space used in the
   cache (@ejgallego, #662, fixes #367 cc: #253 #236 #348)
 - fix Coq performance view display panel (@ejgallego, #663,
   regression in #513)
 - new public VSCode extension API so other extensions can perform
   actions when the user request the goals (@ejgallego, @bhaktishh,
   #672, fixes #538)
 - Support Visual Studio Live Share URIs better (`vsls://`), in
   particular don't try to display goals if the URI is VSLS one
   (@ejgallego, #676)
 - Send performance performance data for the full document
   (@ejgallego, @Alizter, #689, #693)
 - New client option to enable / disable `coq/perfData` (@ejgallego, #717)
 - The `coq-lsp.document` VSCode command will now display the returned
   JSON data in a new editor (@ejgallego, #701)
 - Update server settings on the fly when tweaking them in VSCode.
   Implement `workspace/didChangeConfiguration` (@ejgallego, #702)
 - Always dispose UI elements. This should improve some strange
   behaviors on extension restart (@ejgallego, #708)
 - Support Coq meta-commands (Reset, Reset Initial, Back) They are
   actually pretty useful to hint the incremental engine to ignore
   changes in some part of the document (@ejgallego, #709)
 - New `coq/viewRange` notification, from client to server, than hints
   the scheduler for the visible area of the document; combined with
   the new lazy checking mode, this provides checking on scroll, a
   feature inspired from Isabelle IDE (@ejgallego, #717)
 - Have VSCode wait for full LSP client shutdown on server
   restart. This fixes some bugs on extension restart (finally!)
   (@ejgallego, #719)
 - Center the view if cursor goes out of scope in
   `sentenceNext/sentencePrevious` (@ejgallego, #718)
 - Switch Flèche range encoding to protocol native, this means UTF-16
   code points for now (Léo Stefanesco, @ejgallego, #624, fixes #620,
   #621)
 - Give `Goals` panel focus back if it has lost it (in case of
   multiple panels in the second viewColumn of Vscode) whenever
   user navigates proofs (@Alidra @ejgallego, #722, #725)
 - Add an example of multiple workspaces (@ejgallego, @Blaisorblade,
   #611)
 - Don't show types of un-expanded goals. We should add an option for
   this, but we don't have the cycles (@ejgallego, #730, workarounds
   #525 #652)
 - Support for `.lv / .v.tex` TeX files with embedded Coq code
   (@ejgallego, #727)
 - Don't expand bullet goals at previous levels by default
   (@ejgallego, @Alizter, #731 cc #525)

# coq-lsp 0.1.8: Trick-or-treat
-------------------------------

 - Update VSCode client dependencies, should bring some performance
   improvements to goal pretty printing (@ejgallego, #530)
 - Update goal display colors for light mode so they are actually
   readable now. (@bhaktishh, #539, fixes #532)
 - Added link to Python coq-lsp client by Pedro Carrot and Nuno
   Saavedra (@Nfsaavedra, #536)
 - Properly concatenate warnings from _CoqProject (@ejgallego,
   reported by @mituharu, #541, fixes #540)
 - Fix broken `coq/saveVo` and `coq/getDocument` requests due to a
   parsing problem with extra fields in their requests (@ejgallego,
   #547, reported by @Zimmi48)
 - `fcc` now understands the `--coqlib`, `--coqcorelib`,
   `--ocamlpath`, `-Q` and `-R` arguments (@ejgallego, #555)
 - Describe findlib status in `Workspace.describe`, which is printed
   in the output windows (@ejgallego, #556)
 - `coq-lsp` plugin loader will now be strict in case of a plugin
   failure, the previous loose behavior was more convenient for the
   early releases, but it doesn't make sense now and made things
   pretty hard to debug on the Windows installer (@ejgallego, #557)
 - Add pointers to Windows installers (@ejgallego, #559)
 - Recognize `Goal` and `Definition $id : ... .` as proof starters
   (@ejgallego, #561, reported by @Zimmi48, fixes #548)
 - Provide basic notation information on hover. This is intended for
   people to build their own more refined notation feedback systems
   (@ejgallego, #562)
 - Hover request can now be extended by plugins (@ejgallego, #562)
 - Updated LSP and JS client libs, notably to vscode-languageclient 9
   (@ejgallego, #565)
 - Implement a LIFO document scheduler, this is heavier in the
   background as more documents will be checked, but provides a few
   usability improvements (@ejgallego, #566, fixes #563, reported by
   Ali Caglayan)
 - New lexical qed detection error recovery rule; this makes a very
   large usability difference in practice when editing inside proofs.
   (@ejgallego, #567, fixes #33)
 - `coq-lsp` is now supported by the `coq-nix-toolbox` (@Zimmi48,
   @CohenCyril, #572, via
   https://github.com/coq-community/coq-nix-toolbox/pull/164 )
 - Support for `-rifrom` in `_CoqProject` and in command line
   (`--rifrom`). Thanks to Lasse Blaauwbroek for the report.
   (@ejgallego, #581, fixes #579)
 - Export Query Goals API in VSCode client; this way other extensions
   can implement their own commands that query Coq goals (@amblafont,
   @ejgallego, #576, closes #558)
 - New `pretac` field for preprocessing of goals with a tactic using
   speculative execution, this is experimental for now (@amblafont,
   @ejgallego, #573, helps with #558)
 - Implement `textDocument/selectionRange` request, that will return
   the range of the Coq sentence underlying the cursor. In VSCode,
   this is triggered by the "Expand Selection" command. The
   implementation is partial: we only take into account the first
   position, and we only return a single range (Coq sentence) without
   parents. (@ejgallego, #582)
 - Be more robust to mixed-separator windows paths in workspace
   detection (@ejgallego, #583, fixes #569)
 - Adjust printing breaks in error and message panels (@ejgallego,
   @Alizter, #586, fixes #457 , fixes #458 , fixes #571)

# coq-lsp 0.1.7: Just-in-time
-----------------------------

- Enable web extension support (worker server will happen in next release)
- Improvements and clenaups on hover display, in particular we don't
  print repeated `Notation` strings.
- Fix bug that prevented "Goal after tactic" from working properly.
- Fix "Error message browser becomes non-visible when there are many
  goals" by using a fixed-position separated error display.
- Display the list of pending obligations in info panel.
- Preliminary panel to display document performance data.
- Fix keybinding for the "Show Goals at Point" command
- Hook coq-lsp to ViZX extension
- Warnings settings from `_CoqProject` files are now applied
- Limit the number of messages displayed in the goal window to 101,
  as to workaround slow render of Coq's pretty printing format. This
  is an issue for example in Search where we can get thousand of
  results. We also speed up the rendering a bit by not hashing twice,
  and fix a parameter-passing bug in the React setup.

# coq-lsp 0.1.6: Peek
----------------------

- The information / goal view now uses a new layout-aware printer; the
  if you find any problem the old printer can be enabled in the
  extension options.
- Completion tweaks, for example now ' will trigger end of completion.
- When activating the extension, coq-lsp add to workspace
  configuration an auto-ignore for Coq object files such as .vo, .aux,
  etc...
- Multiple workspace support, use "Add folder to workspace" to handle
  projects with multiple `_CoqProject` files.
- New VS Code commands: start / stop server, save .vo file,
  get serialized version of document.
- `vscode-languageclient` updated to 8.1.0
- New status bar button to toggle server run status
- Scroll active goal into view automatically
- Info on memory and time is now disabled by default, use option
  `coq-lsp.stats_on_hover_option` to re-enable it
- Server greatly improved, see server changelog for more information.

# coq-lsp 0.1.5: Form
----------------------

 - General bugfix and quality-of-life release.
 - Markdown Coq code blocks now must specify "coq" as a language
 - Improved syntax highlighting of Coq markdown files
 - Info panel has been greatly improved
 - Bugfix on message display after the port to React
 - Hover will display type of identifier at point
 - Jump to definition support
 - Goal display handles background goals better, showing preview,
   goals stack, and focusing information
 - The goal display now numbers goals starting with 1 instead of 0
 - Hypotheses with bodies are now correctly displayed
 - Support unicode characters in filenames
 - Stop checking documents after a maximum number of errors (user configurable)
 - Goal view now supports find
 - Display Coq warnings, info and debug messages in info panel
 - Improved outline view, with more details and types
 - Server greatly improved with better error heuristics, see server
   changelog for more information

# coq-lsp 0.1.4: View
----------------------

- The keybinding alt+enter in VSCode is now correctly scoped to be
  only active on Coq files.
- Display an error message when the VSCoq extension is detected to be
  active, as `coq-lsp` and VSCoq don't work well together.
- Display an error message when the client and server versions don't
  match.
- [server-side] Support Unicode files
- [server-side] Unicode completion on `\`, configurable in settings.
- New infoview panel based on React.
- New option in settings to enable Coq Debug mode (and backtraces)
- Fixes a bug that made some `CoqProject` files not to be properly
  detected.

# coq-lsp 0.1.3: Event
----------------------

- Requires coq-lsp server 0.1.3, see full changelog at
  https://github.com/ejgallego/coq-lsp/releases/tag/0.1.3
- Default "show goals" setting is now on cursor movement, thanks to
  upgrade server request serving this is no viable.
- VsCodeVim should work with coq-lsp goal following now (be sure to
  pick the "Command" option in settings)

# coq-lsp 0.1.2: Message
------------------------

- Requires coq-lsp server 0.1.2, see full changelog at
  https://github.com/ejgallego/coq-lsp/releases/tag/0.1.2
- Extension will now enforce that server has the correct version
- The Coq LSP server output window will now show trace information
- Coq Info Panel will now show messages coming from commands such as
  `About` or `Search`
- Coq Info Panel will now show detailed error information.

# coq-lsp 0.1.1: Location
-------------------------

- Requires coq-lsp server 0.1.1, see full changelog at
  https://github.com/ejgallego/coq-lsp/releases/tag/0.1.1%2Bv8.16
- Server greatly improved in terms of responsiveness
- Improved goal panel and interaction mode
- Many new configuration options
- Code will now show a "Coq LSP Server" output window

# coq-lsp 0.1.0: Memory
-----------------------

- First public release: minimal LSP client, with support for a goal panel
