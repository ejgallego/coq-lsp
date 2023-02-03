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

type DetailsP = PropsWithChildren<{
  summary: React.ReactNode;
  open?: boolean;
}>;
function Details({ summary, open, children }: DetailsP) {
  return (
    <details style={{ marginBottom: "1ex" }} open={open ?? true}>
      <summary>{summary}</summary>
      <div style={{ marginLeft: "1ex", marginBottom: "1ex" }}>{children}</div>
    </details>
  );
}

function CoqPp({ content, inline }: { content: string; inline: boolean }) {
  if (inline) {
    return <code>{content}</code>;
  } else {
    return <pre>{content}</pre>;
  }
}

function Message({ message }: { message: string }) {
  let key = objectHash(message);
  return (
    <li key={key}>
      <CoqPp content={message} inline={true} />
    </li>
  );
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

function Hyp({ hyp }: { hyp: Hyp<string> }) {
  return (
    <div className="hypothesis">
      <label className="hname">{hyp.names.join(",")}</label>
      <label className="sep"> : </label>
      <span className="htype">
        <CoqPp content={hyp.ty} inline={true} />
      </span>
      <br />
    </div>
  );
}
type HypsP = { hyps: Hyp<string>[] };
function Hyps({ hyps }: HypsP) {
  return (
    <>
      {hyps.map((v) => {
        let key = objectHash(v);
        return <Hyp key={key} hyp={v} />;
      })}
    </>
  );
}

type GoalP = { goal: Goal<string>; idx: number };

function Goal({ goal, idx }: GoalP) {
  let open = idx == 1;
  return (
    <Details summary={`Goal (${idx})`} open={open}>
      <div className="goalDiv">
        <Hyps hyps={goal.hyps} />
        <hr />
        <div className="pp_goals">
          <span className="goal">
            <CoqPp content={goal.ty} inline={false} />
          </span>
        </div>
      </div>
    </Details>
  );
}

type GoalsListP = {
  goals: Goal<string>[];
  header: string;
  show_on_empty: boolean;
  open: boolean;
};

function GoalsList({ goals, header, open, show_on_empty }: GoalsListP) {
  let count = goals.length;

  if (count == 0 && !show_on_empty) return null;

  return (
    <Details summary={`${header} (${count})`} open={open}>
      {goals.map((value, idx) => {
        let key = objectHash(value);
        return <Goal key={key} goal={value} idx={idx + 1} />;
      })}
    </Details>
  );
}

type GoalsParams = { goals?: GoalConfig<string> };

function Goals({ goals }: GoalsParams) {
  if (!goals) {
    return <p>No goals at this point!</p>;
  }

  return (
    <div className="goalsEnv">
      <GoalsList
        goals={goals.goals}
        header={"Goals"}
        show_on_empty={true}
        open={true}
      />
      <div style={{ marginLeft: "0.5ex" }}>
        <GoalsList
          goals={goals.shelf}
          header={"Shelf"}
          show_on_empty={false}
          open={false}
        />
        <GoalsList
          goals={goals.given_up}
          header={"Given Up"}
          show_on_empty={false}
          open={false}
        />
      </div>
    </div>
  );
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
