// This is the script that is loaded by Coq's webview
import { buildInfoContent } from "./goalRender";
import { GoalAnswer, GoalRequest } from "../../lib/types";
import { WebviewApi } from "vscode-webview";

import "./media/styles.css";

interface CoqInfoViewState {}

const vscode: WebviewApi<CoqInfoViewState> = acquireVsCodeApi();

interface CoqMessageEvent extends MessageEvent {}

function doRenderGoals(goals: GoalAnswer<string>) {
  let infoContainer = document.getElementById("coq-info-body");
  if (infoContainer) {
    infoContainer.innerHTML = buildInfoContent(goals);
  }
}

function doWaitingForInfo(info: GoalRequest) {
  console.log("doWaitingForInfo", info);
}

function doInfoError(e: any) {
  console.log("doInfoError", e);
}

export function infoViewDispatch(event: CoqMessageEvent) {
  switch (event.data.method) {
    case "renderGoals":
      doRenderGoals(event.data.params);
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

window.addEventListener("message", infoViewDispatch);
