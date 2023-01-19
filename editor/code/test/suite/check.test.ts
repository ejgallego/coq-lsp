import * as vscode from "vscode";
import * as path from "node:path";
import "jasmine";

const examplesDir = path.join(__dirname, "..", "..", "..", "examples");

describe("coq-lsp document-check test suite", () => {
  it("Activation event", async () => {
    const ext = vscode.extensions.getExtension("ejgallego.coq-lsp");
    const uri = vscode.Uri.file(path.join(examplesDir, "Rtrigo1.v"));
    await vscode.workspace.openTextDocument(uri);
    expect(ext?.isActive).toBeTrue();
    vscode.commands.executeCommand("workbench.action.closeActiveEditor");
  });
});
