import { WebviewApi } from "vscode-webview";
import { ReactElement, useEffect, useState } from "react";
import {
  VSCodeDataGrid,
  VSCodeDataGridRow,
  VSCodeDataGridCell,
} from "@vscode/webview-ui-toolkit/react";
import "./media/App.css";
import { Range } from "vscode-languageserver-types";
import {
  DocumentPerfParams,
  PerfMessageEvent,
  SentencePerfParams,
} from "../../lib/types";

const vscode: WebviewApi<DocumentPerfParams<Range>> = acquireVsCodeApi();

let empty: DocumentPerfParams<Range> = {
  textDocument: { uri: "", version: 0 },
  summary: "No Data Yet",
  timings: [],
};

function validateViewState(p: DocumentPerfParams<Range>) {
  return (
    p.textDocument &&
    p.summary &&
    p.timings &&
    p.timings[0] &&
    p.timings[0].range &&
    p.timings[0].info
  );
}

function validOrEmpty(
  p: DocumentPerfParams<Range> | undefined
): DocumentPerfParams<Range> {
  // XXX We need to be careful here, when we update the
  // DocumentPerfParams<Range> data type, the saved data here will make the
  // view crash
  if (p && validateViewState(p)) return p;
  else return empty;
}

let init = validOrEmpty(vscode.getState());

function printWords(w: number) {
  if (w < 1024) {
    return `${w.toString()} W`;
  } else if (w < 1024 * 1024) {
    return `${(w / 1024).toFixed(2).toString()} kW`;
  } else {
    return `${(w / 1024 / 1024).toFixed(2).toString()} kW`;
  }
}

// XXX: Would be nice to have typing here, but...
interface PerfCellP {
  field: keyof SentencePerfParams<Range> | string;
  value: any;
}

function SentencePerfCell({ field, value }: PerfCellP) {
  switch (field) {
    case "range":
      let r = value as Range;
      return (
        <span>{`l: ${r.start.line} c: ${r.start.character} -- l: ${r.end.line} c: ${r.end.character}`}</span>
      );
    case "time_hash":
    case "time":
      return <span>{`${value.toFixed(4).toString()} secs`}</span>;
    case "memory":
      return <span>{printWords(value)}</span>;
    case "cache_hit":
      return <span>{value ? "True" : "False"}</span>;
    default:
      return null;
  }
}

interface PerfParamsP {
  idx: number;
  value: SentencePerfParams<Range>;
}

function perfFlatten(v: SentencePerfParams<Range>) {
  return {
    range: v.range,
    time: v.info.time,
    memory: v.info.memory,
    cache_hit: v.info.cache_hit,
    time_hash: v.info.time_hash,
  };
}

function SentencePerfRow({ idx, value }: PerfParamsP) {
  // console.log(value);
  return (
    <VSCodeDataGridRow key={idx + 1}>
      <>
        {Object.entries(perfFlatten(value)).map(([field, value], idx) => {
          return (
            <VSCodeDataGridCell key={idx + 1} grid-column={idx + 1}>
              <SentencePerfCell field={field} value={value} />
            </VSCodeDataGridCell>
          );
        })}
      </>
    </VSCodeDataGridRow>
  );
}

function timeCmp(t1: SentencePerfParams<Range>, t2: SentencePerfParams<Range>) {
  return t2.info.time - t1.info.time;
}

function viewSort(p: DocumentPerfParams<Range>) {
  let textDocument = p.textDocument;
  let summary = p.summary;
  let tlength = p.timings.length;
  let timings = Array.from(p.timings)
    .sort(timeCmp)
    .slice(0, Math.min(30, tlength));
  return { textDocument, summary, timings };
}

function App() {
  let [perfData, setPerfData] = useState(init);

  function viewDispatch(event: PerfMessageEvent) {
    switch (event.data.method) {
      case "update":
        if (!validateViewState(event.data.params)) break;
        let data = viewSort(event.data.params);
        vscode.setState(data);
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
            {Object.entries(
              perfData.timings[0] ? perfFlatten(perfData.timings[0]) : {}
            ).map(([field, _value], idx) => {
              return (
                <VSCodeDataGridCell
                  key={field}
                  grid-column={idx + 1}
                  cell-type="columnheader"
                >
                  {field}
                </VSCodeDataGridCell>
              );
            })}
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
