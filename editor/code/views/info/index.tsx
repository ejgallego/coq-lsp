// This is the script that is loaded by Coq's webview

import React from "react";
import { createRoot } from "react-dom/client";

import InfoPanel from "./Info";
import "./media/index.css";

const container = document.getElementById("root");
const root = createRoot(container!); // createRoot(container!) if you use TypeScript
root.render(
  <React.StrictMode>
    <InfoPanel />
  </React.StrictMode>
);
