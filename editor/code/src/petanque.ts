import { window, InputBoxOptions, TextEditor } from "vscode";
import { BaseLanguageClient, RequestType } from "vscode-languageclient";
import { PetRunParams, PetStartParams } from "../lib/types";

const petStartReq = new RequestType<PetStartParams, number, void>(
  "petanque/start"
);
let client: BaseLanguageClient;

export function petSetClient(newClient: BaseLanguageClient) {
  client = newClient;
}

export const petanqueStart = (editor: TextEditor) => {
  let uri = editor.document.uri.toString();
  let pre_commands = null;

  // Imput theorem name
  let inputOptions: InputBoxOptions = {
    title: "Petanque Start",
    prompt: "Name of the theorem to start a session ",
  };
  window
    .showInputBox(inputOptions)
    .then<PetStartParams>((thm_user) => {
      let thm = thm_user ?? "petanque_debug";
      let params: PetStartParams = { uri, pre_commands, thm };
      return Promise.resolve<PetStartParams>(params);
    })
    .then((params: PetStartParams) => {
      client
        .sendRequest(petStartReq, params)
        .then((id) =>
          window.setStatusBarMessage(`petanque/start succeed ${id}`, 5000)
        )
        .catch((error) => {
          let err_message = error.toString();
          console.log(`error in save: ${err_message}`);
          window.showErrorMessage(err_message);
        });
    });
};

const petRunReq = new RequestType<PetRunParams, any, void>("petanque/run");

export const petanqueRun = (editor: TextEditor) => {
  // XXX Read from user
  let params: PetRunParams = { st: 1, tac: "idtac." };
  client
    .sendRequest(petRunReq, params)
    .then((answer: any) => {
      let res = JSON.stringify(answer);
      window.setStatusBarMessage(`petanque/run succeed ${res}`, 5000);
    })
    .catch((error) => {
      let err_message = error.toString();
      console.log(`error in save: ${err_message}`);
      window.showErrorMessage(err_message);
    });
};
