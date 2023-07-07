import { useEffect, useState, lazy, Suspense } from "react";
import { GoalAnswer, GoalRequest, PpString } from "../../lib/types";

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

// First part, which should be split out is the protocol definition, second part is the UI.
function doWaitingForInfo(info: GoalRequest) {
  console.log("doWaitingForInfo", info);
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

  // We limit the number of messages as to workaround slow rendering
  // in pretty print mode, to be fixed.
  let messages = goals.messages.slice(0, 100);

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
