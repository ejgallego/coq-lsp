"use strict";

/* Documentation Links

https://developer.mozilla.org/en-US/docs/Web/javascript
https://atom.io/docs/api/v1.28.0/AtomEnvironment
https://github.com/atom/atom-languageclient //Here there is also many examples of atom language extensions

*/

const dk = require("./dedukti-editor-view");
const Utils  = require("./utils").default;
const child_process = require("child_process");
const {
  AutoLanguageClient,
  DownloadFile,
  Convert
} = require("atom-languageclient");


class DeduktiLanguageClient extends AutoLanguageClient {

  constructor() {
    // at the opening of Atom
    super();
    this.config = require("./config/settings.json"); // To modify the configuration, check the setting view
  }

  activate() {
    super.activate();
    // create the view and variables we will need to handle the extensions.
    this.deduktiEditorView = new dk.default();
    //Initialize the tools we will need to add interaction within the editor
    Utils.initialize(this);

  }

  getGrammarScopes() {
    return ["source.dedukti"]; //the grammar we defined in dedukti.cson
  }

  getLanguageName() {
    return "Dedukti";
  }

  getServerName() {
    return "lp-lsp";
  }

  startServerProcess(projectPath) {

    // we get the command and args from the setting panel
    var command = atom.config.get("dedukti-editor.lspServerPath");
    var args = atom.config.get("dedukti-editor.lspServerArgs");

    /* // Debug for developper (Ismail)
     var command_test = "./lp-lsp_test";
    const childProcess = child_process.spawn(command_test, args,{
    cwd: "/home/isma/"
    });
    // */

    // a new process is created and send back
    const childProcess = child_process.spawn(command, args);
    return childProcess;
  }

  handleSpawnFailure(err) {
    //TODO: Use the `which` module to provide a better error in the case of a missing server.
    atom.notifications.addError(
      "Error starting the language server: " +
      atom.config.get("dedukti-editor.lspServerPath"),
      {
        dismissable: true,
        description:
        "Please make sure you've followed the Installation section in the README and that the server is functional"
      }
    );
  }

  preInitialization(connection) {

    // we hack onPublishDiagnostics message before it is received by atom and handle positive message
    connection.onPublishDiagnostics = function(callback) {
      let mycallback = function(params) {
        // we add our function before the diagnostics are processed by atomlanguageclient
        params.diagnostics = Utils.updateDiagnostics(params); // the colorBuffer function will color in red and green the editor, remove positive diagnostics and update the panel
        callback(params); // Eventually, the remaining diagnostics are processed by atomlanguageclient
      };
      connection._onNotification(
        { method: "textDocument/publishDiagnostics" },
        mycallback.bind(module.exports) // mycallback needs to be executed within this file context //https://developer.mozilla.org/fr/docs/Web/JavaScript/Reference/Objets_globaux/Function/bind
      );
    };

    //TODO WORKAROUND AGAINST ISSUE #1

  }

}

module.exports = new DeduktiLanguageClient();
