import React, { useEffect, useState } from "react";
import { GoalAnswer, GoalRequest, PpString } from "../../lib/types";

// import "./media/info.css";

// Main panel components
import { FileInfo } from "./FileInfo";
import { Goals } from "./Goals";
import { Messages } from "./Messages";
import { ErrorBrowser } from "./ErrorBrowser";
import { Program } from "./Program";

// First part, which should be split out is the protocol definition, second part is the UI.
function doWaitingForInfo(info: GoalRequest) {
  console.log("doWaitingForInfo", info);
}

export function buildInfoWaiting(info: GoalRequest) {
  let uri = info.textDocument.uri.split("/").at(-1);
  let line = info.position.line + 1;
  let character = info.position.character + 1;
  return `<details open>
    <summary>${uri}:${line}:${character}</summary>
    <em>Waiting for document information, thanks for your patience</em>
    </details>`;
}
  
function doInfoError(e: any) {
  console.log("doInfoError", e);
}

interface RenderGoals {
  method: "renderGoals";
  params: GoalAnswer<PpString>;
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
  let [goals, setGoals] = useState<GoalAnswer<PpString>>();

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

  if (!goals) return null;

  return (
    <FileInfo textDocument={goals.textDocument} position={goals.position}>
      <Goals goals={goals.goals} />
      <Program program={goals.program} />
      <Messages messages={goals.messages} />
      <ErrorBrowser error={goals.error} />
    </FileInfo>
  );
}

export default InfoPanel;
