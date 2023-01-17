// This is the script that is loaded by Coq's webview
import { buildInfoContent } from "./goalRender";
import { GoalAnswer } from "../lib/types";
import { WebviewApi } from "vscode-webview";

import "./media/styles.css";

interface CoqInfoViewState {}

const vscode: WebviewApi<CoqInfoViewState> = acquireVsCodeApi();

interface CoqMessageEvent extends MessageEvent {}

export function infoViewDispatch(event: CoqMessageEvent) {
  let infoContainer = document.getElementById("coq-info-body");
  if (infoContainer && event.data.method == "renderGoals") {
    let goals: GoalAnswer = event.data.params;
    infoContainer.innerHTML = buildInfoContent(goals);
  }
}

window.addEventListener("message", infoViewDispatch);
