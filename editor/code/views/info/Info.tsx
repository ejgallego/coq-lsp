import React, {
  HTMLAttributes,
  PropsWithChildren,
  useEffect,
  useState,
} from "react";
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
  open_if_empty?: boolean;
}>;
function Details({ summary, children }: DetailsP) {
  return (
    <details open={true}>
      <summary>{summary}</summary>
      <div style={{ marginLeft: "1ex" }}>{children}</div>
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

function CoqPpInline({ content }: { content: string }) {
  return <code>{content}</code>;
}

function Message({ message }: { message: string }) {
  return <CoqPp content={message} inline={true} />;
}

type FileInfoParams = PropsWithChildren<GoalRequest>;
function FileInfo({ textDocument, position, children }: FileInfoParams) {
  let uri = textDocument.uri.split("/").at(-1);
  let line = position.line + 1;
  let character = position.character + 1;
  let summary = (
    <>
      {uri}:{line}:{character}
    </>
  );

  return <Details summary={summary}>{children}</Details>;
}

function Hyp({ hyp }: { hyp: Hyp<string> }) {
  return (
    <div className="hypothesis">
      <label className="hname">{hyp.names}</label>
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
        return <Hyp hyp={v} />;
      })}
    </>
  );
}

type GoalP = { goal: Goal<string>; idx: number };
function Goal({ goal, idx }: GoalP) {
  return (
    <Details summary={`Goal (${idx})`}>
      <Hyps hyps={goal.hyps} />
      <hr />
      <div className="pp_goals">
        <span className="goal">
          <CoqPp content={goal.ty} inline={false} />
        </span>
      </div>
    </Details>
  );
}

/* function buildGoalsContent(g: GoalConfig) {
  let goalsBody = detailsOfGoalList(true, "Goals", g.goals);
  let shelfBody =
    g.shelf.length > 0 ? detailsOfGoalList(false, "Shelf", g.shelf) : "";
  let givenBody =
    g.given_up.length > 0
      ? detailsOfGoalList(false, "Given Up", g.given_up)
      : "";
  return `
      ${goalsBody}
      <div style="margin-left: 0.5ex">
        ${shelfBody}
        ${givenBody}
      </div>`;
} */

type GoalsParams = { goals?: GoalConfig<string> };
function Goals({ goals }: GoalsParams) {
  if (!goals) {
    return <p>No goals at this point!</p>;
  }
  let count = goals.goals.length;

  return (
    <Details summary={`Goals (${count})`}>
      <div style={{ marginLeft: "0.5ex" }}>
        {goals.goals.map((value, idx) => {
          return <Goal goal={value} idx={idx} />;
        })}
      </div>
    </Details>
  );
}

type MessageParams = { messages: string[] };
function Messages({ messages }: MessageParams) {
  let count = messages.length;
  return (
    <Details summary={`Messages (${count})`}>
      {messages.map((value, idx) => {
        return <Message message={value} />;
      })}
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
      {/* was: style="margin-left: 1ex; margin-top: 1ex; margin-bottom: 1ex;" */}
      <Goals goals={goals.goals} />

      {/* was: style="margin-left: 1ex; margin-bottom: 1ex;" */}
      <Messages messages={goals.messages} />

      {/* was: style="margin-left: 1ex; margin-bottom: 1ex;" */}
      <ErrorBrowser error={goals.error} />
    </FileInfo>
  );
}

export default InfoPanel;
