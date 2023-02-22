import * as Protocol from "vscode-languageserver-protocol";
import * as LanguageServer from "./LanguageServer";

test("Fully checks ex1.v", async () => {
  let languageServer = await LanguageServer.startAndInitialize();
  await languageServer.sendNotification(
    Protocol.DidOpenTextDocumentNotification.type,
    {
      textDocument: LanguageServer.openExample("ex1.v"),
    }
  );
  let p = new Promise((resolve,reject) => {
    languageServer.onNotification(
      Protocol.PublishDiagnosticsNotification.type,
      async (params) => {
        if (params.diagnostics.length == 0)
        resolve(params);
        else reject(params);
      }
    );
  });
  await p.finally(()=> LanguageServer.exit(languageServer));
});
