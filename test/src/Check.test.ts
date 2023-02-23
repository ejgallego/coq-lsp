import * as Protocol from "vscode-languageserver-protocol";
import * as LanguageServer from "./LanguageServer";

test("Fully checks ex1.v", async () => {
  let languageServer = LanguageServer.start();
  await languageServer.initialize({ trace: "verbose" });

  await languageServer.sendNotification(
    Protocol.DidOpenTextDocumentNotification.type,
    {
      textDocument: LanguageServer.openExample("ex1.v"),
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
