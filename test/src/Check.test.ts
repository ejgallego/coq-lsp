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
  languageServer.onNotification(
    Protocol.PublishDiagnosticsNotification.type,
    async (params) => {
      if (params.diagnostics.length == 0)
        await LanguageServer.exit(languageServer);
    }
  );
});
