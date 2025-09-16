import { useEffect, useState, lazy, Suspense } from "react";
import {
  GoalAnswer,
  GoalRequest,
  PpString,
  CoqMessageEvent,
  ErrorData,
} from "../../lib/types";

// Main panel components
import { FileInfo } from "./FileInfo";
import { Goals } from "./Goals";
import { Messages } from "./Messages";
import { ErrorBrowser } from "./ErrorBrowser";
import { Program } from "./Program";

import "./media/info.css";

// Dynamic import because the project uses CommonJS and the module is an ECMAScript module
// Top level await is supported with other `module` options in tsconfig.json
const VSCodeDivider = lazy(async () => {
  const { VSCodeDivider } = await import("@vscode/webview-ui-toolkit/react");
  return { default: VSCodeDivider };
});

const debugStates = false;

// First part, which should be split out is the protocol definition, second part is the UI.
function doWaitingForInfo(info: GoalRequest) {
  if (debugStates) console.log("doWaitingForInfo", info);
}

function doInfoError(e: any) {
  if (debugStates) console.log("doInfoError", e);
}

export function InfoPanel() {
  let [error, setError] = useState<ErrorData | null>();
  let [goals, setGoals] = useState<GoalAnswer<PpString>>();

  function infoViewDispatch(event: CoqMessageEvent) {
    switch (event.data.method) {
      case "renderGoals":
        setError(null);
        setGoals(event.data.params);
        break;
      case "waitingForInfo":
        doWaitingForInfo(event.data.params);
        break;
      case "infoError":
        setError(event.data.params);
        doInfoError(event.data.params);
        break;
      default:
        console.log("rocq infoview [Info.tsx]: unknown method", event.data);
        break;
    }
  }

  // Set the callback
  useEffect(() => {
    window.addEventListener("message", infoViewDispatch);
    return () => window.removeEventListener("message", infoViewDispatch);
  }, []);

  if (error) {
    return (
      <div className="info-panel-container">
        <div className="info-panel">
          <FileInfo textDocument={error.textDocument} position={error.position}>
            <p>
              <b>{error.message}</b>
            </p>
          </FileInfo>
        </div>
      </div>
    );
  }

  if (!goals) return null;

  // We limit the number of messages as to workaround slow rendering
  // in pretty print mode, to be fixed.
  let messages = goals.messages.slice(0, 100);

  // Normal goal display otherwise
  return (
    <div className="info-panel-container">
      <div className="info-panel">
        <FileInfo textDocument={goals.textDocument} position={goals.position}>
          <Goals goals={goals.goals} />
          <Program program={goals.program} />
          <Messages messages={messages} />
        </FileInfo>
      </div>
      {!goals.error ? null : (
        <div className="error-browser">
          <Suspense>
            <VSCodeDivider />
          </Suspense>
          <ErrorBrowser error={goals.error} />
        </div>
      )}
    </div>
  );
}

export default InfoPanel;
