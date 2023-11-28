import * as Protocol from "vscode-languageserver-protocol";
import * as Types from "vscode-languageserver-types";
import * as LS from "./LanguageServer"; 

async function start() {
  let languageServer = LS.start();
  let initializeParameters: Partial<Protocol.InitializeParams> = {
    rootPath: ".",
    rootUri: ".",
    trace: "verbose",
    workspaceFolders: null,
  };
  let result = await languageServer.initialize(initializeParameters);
  return languageServer;
}

async function sendSimpleDoc(languageServer : LS.LanguageServer, text : string) {
    let textDocument = Types.TextDocumentItem.create(
        "file.v",
        "coq",
        0,
        text,
      );
    await languageServer.sendNotification(
      Protocol.DidOpenTextDocumentNotification.type,
        {
          textDocument,
        },
      );
}
function printDiags(params : Protocol.PublishDiagnosticsParams) {
    console.log(`${params.diagnostics.length} diagnostics received`);
    console.log(params.diagnostics);
}

start().then((ls) => {
    console.log("Starting");
    ls.onNotification(Protocol.PublishDiagnosticsNotification.type, printDiags);
    sendSimpleDoc(ls, "Definition a := 3. Variable (b : nat). Error. ").then(() => {
        setTimeout(() => { ls.exit(); }, 5000)
    })
});
