# unreleased
------------

 - [deps] Bump toolchain so minimal `ppxlib` is 0.26, in order to fix
   some `ppx_import` oddities. This means our lower bound for the Jane
   Street packages is now `v0.15`, which should be fine for the
   foreseeable future (@ejgallego, #813)
 - [workspace] [coq] Support _CoqProject arguments `-type-in-type` and
   `-allow-rewrite-rules` (for 8.20) (@ejgallego, #819)
 - [serlib] Support for ltac2_ltac1 plugin (@ejgallego, #820)
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

# coq-lsp 0.2.0: From Green to Blue
-----------------------------------

 - [deps] merge serlib into coq-lsp. This allow us to drop the SerAPI
   dependency, and will greatly easy the development of tools that
   require AST manipulation (@ejgallego, #698)
 - [fleche] Remove 8.16 compatibility layer (@ejgallego, #747)
 - [fleche] Preserve view hint across document changes. With this
   change, we get local continuous checking mode when the view-port
   heuristic is enabled (@ejgallego, #748)
 - [memo] More precise hashing for Coq states, this improves cache
   performance quite a bit (@ejgallego, #751)
 - [fleche] Enable sharing of `.vo` file parsing. This enables better
   sharing, achieving an almost 50% memory reduction for example when
   opening all of HoTT .v files (@ejgallego, @SkySkimmer, @bhaktishh,
   #744)
 - [memo] Provide API to query Hashtbl stats (@ejgallego, #753)
 - [nix] Add `pet-server` deps to flake.nix (Léo Stefanesco, #754)
 - [coq-lsp] Fix crash on `--help` option (Léo Stefanesco, @ejgallego,
   #754)
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
 - [petanque] Allow `init` to be called multiple times (@ejgallego,
   @gbdrt, #766)
 - [petanque] Faster query for goals status after `run_tac`
   (@ejgallego, #768)
 - [petanque] New parameter `pre_commands` to `start` which allows
   instrumenting the goal before starting the proof (@ejgallego, Alex
   Sanchez-Stern #769)
 - [petanque] New `http_headers={yes,no}` parameter for `pet` json
   shell, plus some improvements on protocol handling (@ejgallego,
   #770)
 - [petanque] Make agent agnostic of environment, allowing embedding
   inside LSP (@ejgallego, #771)
 - [diagnostics] Ensure extra diagnostics info is present in all
   errors, not only on those sentences that did parse successfully
   (@ejgallego, Diego Rivera, #772)
 - [hover] New option `show_universes_on_hover` that will display
   universe data on hover (@ejgallego, @SkySkimmer, #666)
 - [hover] New plugin `unidiff` that will elaborate a summary of
   universe data a file, in particular regarding universes added at
   `Qed` time (@ejgallego, #773)
 - [fleche] Support meta-command `Abort All` (@ejgallego, #774, fixes
   #550)
 - [petanque] Allow memoization control on `petanque/run` via a new
   parameter `memo` (@ejgallego, #780)
 - [lsp] [petanque] Allow acces to `petanque` protocol from the lsp
   server (@ejgallego, #778)
 - [petanque] Always initialize a workspace. This made `pet` crash if
   `--root` was not used and client didn't issue the optimal
   `setWorkspace` call (#782, @ejgallego, @gbdrt)
 - [lsp] [petanque] New methods `state/eq` and `state/hash`; this
   allows clients to implement a client-side hash; equality is
   configurable with different methods; moreover, `petanque/run` can
   compute some extra data like state hashing without a round-trip
   (@ejgallego @gbdrt, #779)
 - [petanque] New methods to hash proof states; use proof state hash
   by default in petanque agent (@ejgallego, @gbdrt, #808)
 - [petanque] New shell method `petanque/toc` that returns a document
   outline in LSP-style (@ejgallego, #794)

# coq-lsp 0.1.10: Hasta el 40 de Mayo _en effect_...
----------------------------------------------------

 - [code] Add `.v.tex` file extension to contributed language support
   (@ejgallego, #740).
 - [code] Don't show the panel on extension activation (@ejgallego,
   #741, fix #737)

# coq-lsp 0.1.9: Hasta el 40 de Mayo...
---------------------------------------

 - new option `show_loc_info_on_hover` that will display parsing debug
   information on hover; previous flag was fixed in code, which is way
   less flexible. This also fixes the option being on in 0.1.8 by
   mistake (@ejgallego, #588)
 - hover plugins can now access the full document, this is convenient
   for many use cases (@ejgallego, #591)
 - fix hover position computation on the presence of Utf characters
   (@ejgallego, #597, thanks to Pierre Courtieu for the report and
   example, closes #594)
 - fix activation bug that prevented extension activation for `.mv`
   files, see discussion in the issues about the upstream policy
   (@ejgallego @r3m0t, #598, cc #596, reported by Théo Zimmerman)
 - require VSCode >= 1.82 in package.json . Our VSCode extension uses
   `vscode-languageclient` 9 which imposes this. (@ejgallego, #599,
   thanks to Théo Zimmerman for the report)
 - `proof/goals` request: new `mode` parameter, to specify goals
   after/before sentence display; renamed `pretac` to `command`, as to
   provide official support for speculative execution (@ejgallego, #600)
 - fix some cases where interrupted computations where memoized
   (@ejgallego, #603)
 - [internal] Flèche [Doc.t] API will now absorb errors on document
   update and creation into the document itself. Thus, a document that
   failed to create or update is still valid, but in the right failed
   state. This is a much needed API change for a lot of use cases
   (@ejgallego, #604)
 - support OCaml 5.1.x (@ejgallego, #606)
 - update progress indicator correctly on End Of File (@ejgallego,
   #605, fixes #445)
 - [plugins] New `astdump` plugin to dump AST of files into JSON and
   SEXP (@ejgallego, #607)
 - errors on save where not properly caught (@ejgallego, #608)
 - switch default of `goal_after_tactic` to `true` (@Alizter,
   @ejgallego, cc: #614)
 - error recovery: Recognize `Defined` and `Admitted` in lex recovery
   (@ejgallego, #616)
 - completion: correctly understand UTF-16 code points on completion
   request (Léo Stefanesco, #613, fixes #531)
 - don't trigger the goals window in general markdown buffer
   (@ejgallego, #625, reported by Théo Zimmerman)
 - allow not to postpone full document requests (#626, @ejgallego)
 - new configuration value `check_only_on_request` which will delay
   checking the document until a request has been made (#629, cc: #24,
   @ejgallego)
 - fix typo on package.json configuration section (@ejgallego, #645)
 - be more resilient with invalid _CoqProject files (@ejgallego, #646)
 - support for Coq 8.16 has been abandoned due to lack of dev
   resources (@ejgallego, #649)
 - new option `--no_vo` for `fcc`, which will skip the `.vo` saving
   step. `.vo` saving is now an `fcc` plugins, but for now, it is
   enabled by default (@ejgallego, #650)
 - depend on `memprof-limits` on OCaml 4.x (@ejgallego, #660)
 - bump minimal OCaml version to 4.12 due to `memprof-limits`
   (@ejgallego, #660)
 - monitor all Coq-level calls under an interruption token
   (@ejgallego, #661)
 - interpret require thru our own custom execution env-aware path
   (@bhaktishh, @ejgallego, #642, #643, #644)
 - new `coq-lsp.plugin.goaldump` plugin, as an example on how to dump
   goals from a document (@ejgallego @gbdrt, #619)
 - new trim command (both in the server and in VSCode) to liberate
   space used in the cache (@ejgallego, #662, fixes #367 cc: #253 #236
   #348)
 - fix Coq performance view display (@ejgallego, #663, regression in
   #513)
 - Added new heatmap feature allowing timing data to be seen in the
   editor. Can be enabled with the `Coq LSP: Toggle heatmap`
   command. Can be configured to show memory usage. Colors and
   granularity are configurable. (@Alizter and @ejgallego, #686,
   grants #681).
 - allow more than one input position in `selectionRange` LSP call
   (@ejgallego, #667, fixes #663)
 - new VSCode commands to allow to move one sentence backwards /
   forward, this is particularly useful when combined with lazy
   checking mode (@ejgallego, #671, fixes #263, fixes #580)
 - VSCode commands `coq-lsp.sentenceNext` / `coq-lsp.sentencePrevious`
   are now bound by default to `Alt + N` / `Alt + P` keybindings
   (@ejgallego, #718)
 - change diagnostic `extra` field to `data`, so we now conform to the
   LSP spec, include the data only when the `send_diags_extra_data`
   server-side option is enabled (@ejgallego, #670)
 - include range of full sentence in error diagnostic extra data
   (@ejgallego, #670 , thanks to @driverag22 for the idea, cc: #663).
 - The `coq-lsp.pp_type` VSCode client option now takes effect
   immediately, no more need to restart the server to get different
   goal display formats (@ejgallego, #675)
 - new public VSCode extension API so other extensions can perform
   actions when the user request the goals (@ejgallego, @bhaktishh,
   #672, fixes #538)
 - Support Visual Studio Live Share URIs better (`vsls://`), in
   particular don't try to display goals if the URI is VSLS one
   (@ejgallego, #676)
 - New `InjectRequire` plugin API for plugins to be able to instrument
   the default import list of files (@ejgallego @corwin-of-amber,
   #679)
 - Add `--max_errors=n` option to `fcc`, this way users can set
   `--max_errors=0` to imitate `coqc` behavior (@ejgallego, #680)
 - Fix `fcc` exit status when checking terminates with fatal errors
   (@ejgallego, @Alizter, #680)
 - Fix install to OPAM switches from `main` branch (@ejgallego, #683,
   fixes #682, cc #479 #488, thanks to @Hazardouspeach for the report)
 - New `--int_backend={Coq,Mp}` command line parameter to select the
   interruption method for Coq (@ejgallego, #684)
 - Update `package-lock.json` for latest bugfixes (@ejgallego, #687)
 - Update Nix flake enviroment (@Alizter, #684 #688)
 - Update `prettier` (@Alizter @ejgallego, #684 #688)
 - Store original performance data in the cache, so we now display the
   original timing and memory data even for cached commands (@ejgallego, #693)
 - Fix type errors in the Performance Data Notifications (@ejgallego,
   @Alizter, #689, #693)
 - Send performance performance data for the full document
   (@ejgallego, @Alizter, #689, #693)
 - Better types `coq/perfData` call (@ejgallego @Alizter, #689)
 - New server option to enable / disable `coq/perfData` (@ejgallego, #689)
 - New client option to enable / disable `coq/perfData` (@ejgallego, #717)
 - The `coq-lsp.document` VSCode command will now display the returned
   JSON data in a new editor (@ejgallego, #701)
 - Update server settings on the fly when tweaking them in VSCode.
   Implement `workspace/didChangeConfiguration` (@ejgallego, #702)
 - [Coq API] Add functions to retrieve list of declarations done in
   .vo files (@ejgallego, @eytans, #704)
 - New `petanque` API to interact directly with Coq's proof
   engine. (@ejgallego, @gbdrt, Laetitia Teodorescu #703, thanks to
   Alex Sanchez-Stern for many insightful feedback and testing)
 - New `petanque` JSON-RPC `pet.exe`, which can be used à la SerAPI
   to perform proof search and more (@ejgallego, @gbdrt, #705)
 - New `pet-server.exe` TCP server for keep-alive sessions (@gbdrt,
   #697)
 - Always dispose UI elements. This should improve some strange
   behaviors on extension restart (@ejgallego, #708)
 - [code] Added new heatmap feature allowing timing data to be seen in
   the editor. Can be enabled with the `Coq LSP: Toggle heatmap`
   comamnd. Can be configured to show memory usage. Colors and
   granularity are configurable. (@Alizter and @ejgallego, #686,
   grants #681).
 - [server] Support Coq meta-commands (Reset, Reset Initial, Back)
   They are actually pretty useful to hint the incremental engine to
   ignore changes in some part of the document (@ejgallego, #709)
 - JSON-RPC library now supports all kind of incoming messages
   (@ejgallego, #713)
 - [code/server] New `coq/viewRange` notification, from client to
   server, than hints the scheduler for the visible area of the
   document; combined with the new lazy checking mode, this provides
   checking on scroll, a feature inspired from Isabelle IDE
   (@ejgallego, #717)
 - [code] Have VSCode wait for full LSP client shutdown on server
   restart. This fixes some bugs on extension restart (finally!)
   (@ejgallego, #719)
 - [code] Center the view if cursor goes out of scope in
   `sentenceNext/sentencePrevious` (@ejgallego, #718)
 - Switch Flèche range encoding to protocol native, this means UTF-16
   code points for now (Léo Stefanesco, @ejgallego, #624, fixes #620,
   #621)
 - Give `Goals` panel focus back if it has lost it (in case of
   multiple panels in the second viewColumn of Vscode) whenever
   user navigates proofs (@Alidra @ejgallego, #722, #725)
 - `fcc`: new option `--diags_level` to control whether Coq's notice
   and info messages appear as diagnostics
 - [code] Display the continous/on-request checking mode in the status bar,
   allow to change it by clicking on it (@ejgallego, #721)
 - Add an example of multiple workspaces (@ejgallego, @Blaisorblade,
   #611)
 - Don't show types of un-expanded goals. We should add an option for
   this, but we don't have the cycles (@ejgallego, #730, workarounds
   #525 #652)
 - Support for `.lv / .v.tex` TeX files with embedded Coq code
   (@ejgallego, #727)
 - Don't expand bullet goals at previous levels by default
   (@ejgallego, @Alizter, #731 cc #525)
 - [petanque] Return basic goal information after `run_tac`, so we
   avoid a `goals` round-trip for each tactic (@gbdrt, @ejgallego,
   #733)
 - [coq] Add support for reading glob files metadata (@ejgallego,
   #735)
 - [petanque] Return extra premise information: file name, position,
   raw_text, using the above support for reading .glob files
   (@ejgallego, #735)
 - [code] Display server status using the `LanguageStatusItem`
   facility, for now we display version and checking status
   information (moved from #721), and we also allow to toggle the
   checking mode from there (@ejgallego, #728)

# coq-lsp 0.1.8.1: Spring fix
-----------------------------

 - call to VizCar vscode extension, mirroring behavior for
   vizx. (@bhaktishh, #655)

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

 - New command line compiler `fcc`. `fcc` allows to access most
   features of `coq-lsp` without the need for a command line client,
   and it has been designed to be extensible and machine-friendly
   (@ejgallego, #507, fixes #472)
 - Enable web extension support. For now this will not try to start
   the coq-lsp worker as it is not yet built. (@ejgallego, #430, fixes
   #234)
 - Improvements and clenaups on hover display, in particular we don't
   print repeated `Notation` strings (@ejgallego, #422)
 - Don't fail on missing serlib plugins, they are indeed an
   optimization; this mostly impacts 8.16 by lowering the SerAPI
   requirements (@ejgallego, #421)
 - Fix bug that prevented "Goal after tactic" from working properly
   (@ejgallego, #438, reported by David Ilcinkas)
 - Fix "Error message browser becomes non-visible when there are many
   goals" by using a fixed-position separated error display (@TDiazT,
   #455, fixes #441)
 - Message about workspace detection was printing the wrong file,
   (@ejgallego, #444, reported by Alex Sanchez-Stern)
 - Display the list of pending obligations in info panel (@ejgallego,
   #262)
 - Preliminary support to display document performance data in panel
   (@ejgallego, #181)
 - Fix cases when workspace / root URIs are `null`, as per LSP spec,
   (#453 , reported by orilahav, fixes #283)
 - Pass implicit argument information to hover printer (@ejgallego, #453,
   fixes #448)
 - Fix keybinding for the "Show Goals at Point" command (@4ever2, #460)
 - Alert when `rootPath` is relative (#465, @ejgallego, report by Alex
   Sanchez-Stern)
 - Hook coq-lsp to ViZX extension (@bhaktishh, #469)
 - `proof/goals` request now takes an optional formatting parameter
   so clients can specify it per-request (@ejgallego, @bhaktishh, #470)
 - New command line argument `--idle-delay=$secs` that controls how
   much an idle server will sleep before going back to request
   processing. Default setting is `0.1`, using more aggressive
   settings like `0.01` can decrease latency of requests by ~4x
   (@ejgallego, @hazardouspeach, #467, #471)
 - Warnings from `_CoqProject` files are now applied (@ejgallego,
   reported by @arthuraa, #500)
 - Be more resilient when serializing unknowns Asts (@ejgallego, #503,
   reported by Gijs Pennings)
 - Coq's STM is not linked anymore to `coq-lsp` (@ejgallego, #511)
 - More granular options `send_perf_data` `send_diags`, `verbosity`
   will set them now (@ejgallego, #517)
 - Preliminary plugin API for completion events (@ejgallego, #518,
   fixes #506)
 - Limit the number of messages displayed in the goal window to 101,
   as to workaround slow render of Coq's pretty printing format. This
   is an issue for example in Search where we can get thousand of
   results. We also speed up the rendering a bit by not hashing twice,
   and fix a parameter-passing bug. (@ejgallego, #523, reported by
   Anton Podkopaev)

# coq-lsp 0.1.6: Peek
---------------------

 - The info / goal view now uses jsCoq's client-side rendering, with
   better highlighting and layout rendering (@artagnon, @ejgallego,
   #143, fixes #96)
 - Printing method is now configurable by the user (@ejgallego, #143,
   fixes #321)
 - Trigger completion on quote char "'" (@ejgallego, #350)
 - Fix typo on keybinding config for show goals (@tomtomjhj, #357)
 - New request `coq/getDocument` to get serialized full document
   contents. Thanks to Clément Pit-Claudel for feedback and ideas.
   (@ejgallego, #350)
 - Auto-ignore Coq object files; can be disabled in config
   (@ejgallego, #365)
 - Support workspaces with multiple roots, this is very useful for
   projects that contain several `_CoqProject` files in different
   directories (@ejgallego, #374)
 - Add VS Code commands to start / stop the server (@ejgallego, #377,
   cc #209)
 - Fix bug that made the server not exit on `exit` LSP notification
   (@artagnon, @ejgallego, #375, fixes #230)
 - Lay the foundation for server tests (@artagnon, #356)
 - Remove the `coq-lsp.ok_diagnostics` setting (@artagnon, #129)
 - Print abbreviations on hover (@ejgallego, #384)
 - Print hover types without parenthesis (@ejgallego, #384)
 - Parse identifiers with dot for hover and jump to definition
   (@ejgallego, #385)
 - Update `vscode-languageclient` to 8.1.0 (@ejgallego, @Alizter,
   #383, fixes #273)
 - Fix typo on max_errors checking, this made coq-lsp stop on the
   number of total diagnostics, instead of only errors (@ejgallego,
   #386)
 - Hover symbol information: hypothesis names must shadow globals of
   the same name (@ejgallego, #391, fixes #388)
 - De-schedule document on didClose, otherwise the scheduler will keep
   trying to resume it if it didn't finish (@ejgallego, #392)
 - Hover symbol information: correctly handle identifiers before '.'
   and containing a quote (') themselves (@ejgallego, #393)
 - Add children entries to the table-of-contents (@ejgallego, #394)
 - Invalidate Coq's imperative cache on error (@ejgallego, @r-muhairi,
   #395)
 - Add status bar button to toggle server run status (@ejgallego,
   @Alizter, #378, closes #209)
 - Support for `COQLIB` and `COQCORELIB` environment variables, added
   `--coqcorelib` command line argument (@ejgallego, #403)
 - Protocol infrastructure for code lenses (@ejgallego, #396)
 - Set binary mode for protocol input / output (@ejgallego, #408)
 - Allow to set `ocamlpath` from the command line (@ejgallego, #408)
 - Windows support (@ejgallego, @jim-portegies, #408)
 - Scroll active goal into view (@ejgallego, #410, fixes #381)
 - Server status icon will now react properly to fatal server errors
   (@ejgallego, reported by @Alizter, #411, fixes #399)
 - Info on memory and time is now disabled by default, new option
   `coq-lsp.stats_on_hover_option` to re-enable it (@ejgallego, #412,
   fixes #398).
 - `coq-lsp` can now save `.vo` files for files opened in the
   editor. Use the new "Save to .vo" command, or the new protocol
   `coq/saveVo` request (@ejgallego, #417, fixes #339)

# coq-lsp 0.1.5.1: Path
-----------------------

 - Fix handling of `COQPATH` and `OCAMLPATH` (@ejgallego, #364)

# coq-lsp 0.1.5: Form
---------------------

 - Fix a bug when trying to complete in an empty file (@ejgallego,
   #270)
 - Fix a bug with the position reported by the `$/coq/fileProgress`
   notification (#270)
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
 - Hypotheses with bodies are now correctly displayed (@ejgallego,
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
   #288, fixes #304, based on jsCoq code by Shachar Itzhaky)
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
 - [internal] Error recovery can now execute full Coq commands as to
   amend states, required for #319 (@ejgallego, #320)
 - Auto-admit the previous bullet goal when a new bullet cannot be
   opened due to an unsolved previous bullet. This also works for {}
   focusing operators. This is very useful when navigating bulleted
   proofs (@ejgallego, @Alizter, #319, fixes #300)
 - Store Ast.Info.t incrementally (@ejgallego, #337, fixes #316)
 - Basic jump to definition support; due to lack of workspace
   metadata, this only works inside the same file (@ejgallego, #318)
 - Show type of identifiers at point on hover (@ejgallego, #321, cc:
   #164)

# coq-lsp 0.1.4: View
---------------------

 - Support for OCaml 4.11 (@ejgallego, #184)
 - The keybinding alt+enter in VSCode is now correctly scoped to be
   only active on Coq files (@artagnon, #188)
 - Support Unicode files (@ejgallego, #200, fixes #193, fixes #197)
 - The info / goal view is now script enabled and does client-side
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
