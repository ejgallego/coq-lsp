import { LanguageStatusItem, LanguageStatusSeverity, languages } from "vscode";
import { NotificationType } from "vscode-languageclient";

import { CoqSelector } from "./config";

import { CoqServerVersion, CoqServerStatus } from "../lib/types";

export const coqServerVersion = new NotificationType<CoqServerVersion>(
  "$/coq/serverVersion"
);

export const coqServerStatus = new NotificationType<CoqServerStatus>(
  "$/coq/serverStatus"
);

// We should likely have one class per item, but not a big deal yet
export class CoqLanguageStatus {
  // Checking and what
  status: LanguageStatusItem;
  // Version info
  version: LanguageStatusItem;
  // Root: one or multiple, to be done soon
  // root : LanguageStatusItem;

  constructor(
    version: CoqServerVersion,
    status: CoqServerStatus,
    lazy_mode: boolean
  ) {
    // Version info
    this.version = languages.createLanguageStatusItem(
      "coq.version",
      CoqSelector.all
    );
    this.version.name = "Version";

    // Server status
    this.status = languages.createLanguageStatusItem(
      "coq.status",
      CoqSelector.all
    );
    this.status.name = "Running Status";

    // this.status.command = "start continous toogle continous";
    // root = languages.createLanguageStatusItem("coq.root", CoqSelector.all);

    this.updateVersion(version);
    this.updateStatus(status, lazy_mode);
  }

  updateVersion(version: CoqServerVersion) {
    this.version.text = `coq-lsp ${version.coq_lsp}`;
    this.version.detail = `Coq ${version.coq}, OCaml ${version.ocaml}`;
  }

  updateStatus(status: CoqServerStatus, lazy_mode: boolean) {
    let command = lazy_mode
      ? {
          title: "Enable Continous Mode",
          command: "coq-lsp.toggle_mode",
        }
      : {
          title: "Enable On-Demand Mode",
          command: "coq-lsp.toggle_mode",
          args: true,
        };

    let status_name = lazy_mode ? "On-demand" : "Continous";

    if (status.status == "Busy") {
      this.status.busy = true;
      this.status.text = `coq-lsp: Checking ${status.modname}`;
      this.status.detail = `set mode`;
      this.status.command = command;
      this.status.severity = LanguageStatusSeverity.Information;
    } else if (status.status == "Idle") {
      // Idle
      this.status.busy = false;
      this.status.text = `coq-lsp: Idle (${status_name} |${status.mem})`;
      this.status.detail = "";
      this.status.command = command;
      this.status.severity = LanguageStatusSeverity.Information;
    } else if (status.status == "Stopped") {
      this.status.busy = false;
      this.status.text = `Stopped`;
      this.status.detail = "";
      this.status.command = { title: "Start Server", command: "coq-lsp.start" };
      this.status.severity = LanguageStatusSeverity.Error;
    }
  }

  dispose() {
    this.status.dispose();
    this.version.dispose();
    // root.dispose();
  }
}

export const defaultVersion: CoqServerVersion = {
  coq: "N/A",
  ocaml: "N/A",
  coq_lsp: "N/A",
};
export const defaultStatus: CoqServerStatus = { status: "Idle", mem: "" };
