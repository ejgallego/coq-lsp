import * as Protocol from "vscode-languageserver-protocol";
import * as LanguageServer from "./LanguageServer";

test("startup and shutdown", async () => {
  await LanguageServer.start().exit();
});

test("initialize with empty capabilities and rootPath (absolute)", async () => {
  let languageServer = LanguageServer.start();
  let capabilities: Protocol.ClientCapabilities = {};
  let initializeParameters: Protocol.InitializeParams = {
    processId: process.pid,
    rootPath: ".",
    rootUri: null,
    capabilities: capabilities,
    workspaceFolders: [],
  };
  let result = await languageServer.sendRequest(
    Protocol.InitializeRequest.type,
    initializeParameters,
  );
  expect(result.capabilities).toBeTruthy();
  await languageServer.exit();
});

test("initialize with empty capabilities and rootURI", async () => {
  let languageServer = LanguageServer.start();
  let capabilities: Protocol.ClientCapabilities = {};
  let initializeParameters: Protocol.InitializeParams = {
    processId: process.pid,
    rootUri: LanguageServer.toURI(__dirname),
    capabilities: capabilities,
    workspaceFolders: [],
  };
  let result = await languageServer.sendRequest(
    Protocol.InitializeRequest.type,
    initializeParameters,
  );
  expect(result.capabilities).toBeTruthy();
  await languageServer.exit();
});
