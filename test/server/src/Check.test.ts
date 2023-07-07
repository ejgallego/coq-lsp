import * as Protocol from "vscode-languageserver-protocol";
import * as Types from "vscode-languageserver-types";
import * as LanguageServer from "./LanguageServer";

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
test("Open file with wrong URI", async () => {
  let languageServer = LanguageServer.start();

  // Enable to print server debug messages
  // languageServer.onNotification(Protocol.LogTraceNotification.type, (msg : Protocol.LogTraceParams) => {
  //   console.log(msg);
  // });

  // languageServer.onNotification(Protocol.LogMessageNotification.type, (msg : Protocol.LogMessageParams) => {
  //   console.log(msg);
  // });

  let initializeParameters: Partial<Protocol.InitializeParams> = {
    rootPath: ".",
    rootUri: ".",
    trace: "verbose",
    workspaceFolders: null,
  };

  await languageServer.initialize(initializeParameters);

  let textDocument = Types.TextDocumentItem.create(
    "wrong_file.v",
    "coq",
    0,
    "Definition a := 3."
  );

  await languageServer.sendNotification(
    Protocol.DidOpenTextDocumentNotification.type,
    {
      textDocument,
    }
  );
  let p = new Promise<Protocol.PublishDiagnosticsParams>((resolve) => {
    languageServer.onNotification(
      Protocol.PublishDiagnosticsNotification.type,
      resolve
    );
  });

  const checkDiags = async (params: Protocol.PublishDiagnosticsParams) => {
    if (params.diagnostics.length == 0) return "ok";
    else throw "wrong number of diags";
  };

  await p.then(checkDiags).finally(languageServer.exit);
  // write more compositionally:
  // await l.diags.next().then(checkDiags).finally(l.exit);
});

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
test("Open non-existing file, with URI", async () => {
  let languageServer = LanguageServer.start();
  await languageServer.initialize({ trace: "verbose" });

  let textDocument = LanguageServer.openExampleEphemeral(
    "ephemeral.v",
    "Definition a := 3."
  );

  await languageServer.sendNotification(
    Protocol.DidOpenTextDocumentNotification.type,
    {
      textDocument,
    }
  );
  let p = new Promise<Protocol.PublishDiagnosticsParams>((resolve) => {
    languageServer.onNotification(
      Protocol.PublishDiagnosticsNotification.type,
      resolve
    );
  });

  const checkDiags = async (params: Protocol.PublishDiagnosticsParams) => {
    if (params.diagnostics.length == 0) return "ok";
    else throw "wrong number of diags";
  };

  await p.then(checkDiags).finally(languageServer.exit);
  // write more compositionally:
  // await l.diags.next().then(checkDiags).finally(l.exit);
});

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
test("Fully checks ex1.v", async () => {
  let languageServer = LanguageServer.start();
  await languageServer.initialize({ trace: "verbose" });

  let textDocument = LanguageServer.openExample("ex1.v");
  await languageServer.sendNotification(
    Protocol.DidOpenTextDocumentNotification.type,
    {
      textDocument,
    }
  );
  let p = new Promise<Protocol.PublishDiagnosticsParams>((resolve) => {
    languageServer.onNotification(
      Protocol.PublishDiagnosticsNotification.type,
      resolve
    );
  });

  const checkDiags = async (params: Protocol.PublishDiagnosticsParams) => {
    if (params.diagnostics.length == 0) return "ok";
    else throw "wrong number of diags";
  };

  await p.then(checkDiags).finally(languageServer.exit);
  // write more compositionally:
  // await l.diags.next().then(checkDiags).finally(l.exit);
});
