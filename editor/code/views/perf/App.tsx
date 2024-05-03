import { WebviewApi } from "vscode-webview";
import React, { ReactElement, useEffect, useState } from "react";
import {
  VSCodeDataGrid,
  VSCodeDataGridRow,
  VSCodeDataGridCell,
} from "@vscode/webview-ui-toolkit/react";
import "./media/App.css";
import { Range } from "vscode-languageserver-types";
import { DocumentPerfParams } from "../../lib/types";

const vscode: WebviewApi<DocumentPerfParams> = acquireVsCodeApi();

let empty: DocumentPerfParams = {
  textDocument: { uri: "", version: 0 },
  summary: "No Data Yet",
  timings: [],
};

let init = vscode.getState() || empty;

interface CoqMessageEvent extends MessageEvent {}

function printWords(w: number) {
  if (w < 1024) {
    return `${w.toString()} W`;
  } else if (w < 1024 * 1024) {
    return `${(w / 1024).toFixed(2).toString()} kW`;
  } else {
    return `${(w / 1024 / 1024).toFixed(2).toString()} kW`;
  }
}

function SentencePerfCell({ field, value }) {
  switch (field) {
    case "range":
      let r = value as Range;
      return (
        <span>{`l: ${r.start.line} c: ${r.start.character} -- l: ${r.end.line} c: ${r.end.character}`}</span>
      );
    case "time":
      return <span>{`${value.toFixed(4).toString()} secs`}</span>;
    case "memory":
      return <span>{printWords(value)}</span>;
    default:
      return null;
  }
}
function SentencePerfRow({ idx, value }) {
  return (
    <VSCodeDataGridRow key={idx + 1}>
      <>
        {Object.entries(value).map(([field, _value], idx) => {
          return (
            <VSCodeDataGridCell key={idx + 1} grid-column={idx + 1}>
              <SentencePerfCell field={field} value={value[field]} />
            </VSCodeDataGridCell>
          );
        })}
      </>
    </VSCodeDataGridRow>
  );
}

function App() {
  let [perfData, setPerfData] = useState(init);

  function viewDispatch(event: CoqMessageEvent) {
    switch (event.data.method) {
      case "update":
        vscode.setState(event.data.params);
        setPerfData(event.data.params);
        break;
      case "reset":
        vscode.setState(empty);
        setPerfData(empty);
        break;
      default:
        console.log("unknown method", event.data);
        break;
    }
  }
  // Listener for notifications
  useEffect(() => {
    window.addEventListener("message", viewDispatch);
  }, []);

  return (
    <main>
      <pre>uri: {perfData.textDocument.uri}</pre>
      <pre>summary: {perfData.summary}</pre>
      <VSCodeDataGrid aria-label="Timing Information">
        <VSCodeDataGridRow key={0} rowType="sticky-header">
          <>
            {Object.entries(perfData.timings[0] ?? []).map(
              ([field, _value], idx) => {
                return (
                  <VSCodeDataGridCell
                    key={field}
                    grid-column={idx + 1}
                    cell-type="columnheader"
                  >
                    {field}
                  </VSCodeDataGridCell>
                );
              }
            )}
          </>
        </VSCodeDataGridRow>
        <>
          {perfData.timings.map((value, idx) => {
            return <SentencePerfRow idx={idx} value={value} />;
          })}
        </>
      </VSCodeDataGrid>
    </main>
  );
}

export default App;
