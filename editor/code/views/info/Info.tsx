import React, { PropsWithChildren, useEffect, useState } from "react";
import {
  VersionedTextDocumentIdentifier,
  Position,
} from "vscode-languageserver-types";
import {
  Goal,
  GoalAnswer,
  GoalConfig,
  GoalRequest,
  Hyp,
} from "../../lib/types";
import objectHash from "object-hash";
import "./media/info.css";
import { Details } from "./Details";
import { Message } from "./Message";
import { CoqPp } from "./CoqPp";
import { Goals } from "./Goals";

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

type FileInfoParams = PropsWithChildren<GoalRequest>;
function FileInfo({ textDocument, position, children }: FileInfoParams) {
  let uri = textDocument.uri.split("/").at(-1);
  let line = position.line + 1;
  let character = position.character + 1;
  let summary = (
    <span>
      {uri}:{line}:{character}
    </span>
  );

  return <Details summary={summary}>{children}</Details>;
}

type MessageParams = { messages: string[] };

function Messages({ messages }: MessageParams) {
  let count = messages.length;
  let open = count > 0;
  return (
    <Details summary={`Messages (${count})`} open={open}>
      <ul className="messageList">
        {messages.map((value, idx) => {
          let key = objectHash(value);
          return <Message key={key} message={value} />;
        })}
      </ul>
    </Details>
  );
}

type ErrorBrowserParams = { error?: string };

function ErrorBrowser({ error }: ErrorBrowserParams) {
  if (!error) return null;

  return (
    <Details summary={"Error Browser"}>
      <CoqPp content={error} inline={false} />
    </Details>
  );
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
