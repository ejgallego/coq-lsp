import React, { useEffect, useState } from "react";
import {
  VersionedTextDocumentIdentifier,
  Position,
} from "vscode-languageserver-types";
import { GoalAnswer, GoalRequest } from "../../lib/types";

// import "./media/info.css";

// Main panel components
import { FileInfo } from "./FileInfo";
import { Goals } from "./Goals";
import { Messages } from "./Messages";
import { ErrorBrowser } from "./ErrorBrowser";

// First part, which should be split out is the protocol definition, second part is the UI.
function doWaitingForInfo(info: GoalRequest) {
  console.log("doWaitingForInfo", info);
}

function doInfoError(e: any) {
  console.log("doInfoError", e);
}
let initGoals: GoalAnswer<string> = {
  textDocument: VersionedTextDocumentIdentifier.create("Welcome to coq-lsp", 0),
  position: Position.create(0, 0),
  messages: [],
};
interface RenderGoals {
  method: "renderGoals";
  params: GoalAnswer<string>;
}
interface WaitingForInfo {
  method: "waitingForInfo";
  params: GoalRequest;
}
interface InfoError {
  method: "infoError";
  params: any;
}
interface CoqMessageEvent extends MessageEvent {
  data: RenderGoals | WaitingForInfo | InfoError;
}

export function InfoPanel() {
  let [goals, setGoals] = useState<GoalAnswer<string>>(initGoals);

  function infoViewDispatch(event: CoqMessageEvent) {
    switch (event.data.method) {
      case "renderGoals":
        setGoals(event.data.params);
        break;
      case "waitingForInfo":
        doWaitingForInfo(event.data.params);
        break;
      case "infoError":
        doInfoError(event.data.params);
        break;
      default:
        console.log("unknown method", event.data);
        break;
    }
  }

  // Set the callback
  useEffect(() => {
    window.addEventListener("message", infoViewDispatch);
    return () => window.removeEventListener("message", infoViewDispatch);
  }, []);

  return (
    <FileInfo textDocument={goals.textDocument} position={goals.position}>
      <Goals goals={goals.goals} />
      <Messages messages={goals.messages} />
      <ErrorBrowser error={goals.error} />
    </FileInfo>
  );
}

export default InfoPanel;
