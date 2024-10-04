import { TextDocumentFilter } from "vscode-languageclient";

export interface CoqLspServerConfig {
  client_version: string;
  eager_diagnostics: boolean;
  goal_after_tactic: boolean;
  show_coq_info_messages: boolean;
  show_notices_as_diagnostics: boolean;
  admit_on_bad_qed: boolean;
  debug: boolean;
  unicode_completion: "off" | "normal" | "extended";
  max_errors: number;
  pp_type: 0 | 1 | 2;
  show_stats_on_hover: boolean;
  show_loc_info_on_hover: boolean;
  show_universes_on_hover: boolean;
  check_only_on_request: boolean;
  send_perf_data: boolean;
}

export namespace CoqLspServerConfig {
  export function create(
    client_version: string,
    wsConfig: any
  ): CoqLspServerConfig {
    return {
      client_version: client_version,
      eager_diagnostics: wsConfig.eager_diagnostics,
      goal_after_tactic: wsConfig.goal_after_tactic,
      show_coq_info_messages: wsConfig.show_coq_info_messages,
      show_notices_as_diagnostics: wsConfig.show_notices_as_diagnostics,
      admit_on_bad_qed: wsConfig.admit_on_bad_qed,
      debug: wsConfig.debug,
      unicode_completion: wsConfig.unicode_completion,
      max_errors: wsConfig.max_errors,
      pp_type: wsConfig.pp_type,
      show_stats_on_hover: wsConfig.show_stats_on_hover,
      show_loc_info_on_hover: wsConfig.show_loc_info_on_hover,
      show_universes_on_hover: wsConfig.show_universes_on_hover,
      check_only_on_request: wsConfig.check_only_on_request,
      send_perf_data: wsConfig.send_perf_data,
    };
  }
}

export enum ShowGoalsOnCursorChange {
  Never = 0,
  OnMouse = 1,
  OnMouseAndKeyboard = 2,
  OnMouseKeyboardCommand = 3,
}

export interface CoqLspClientConfig {
  show_goals_on: ShowGoalsOnCursorChange;
  pp_format: "Pp" | "Str";
  check_on_scroll: boolean;
}

function pp_type_to_pp_format(pp_type: 0 | 1 | 2): "Pp" | "Str" {
  switch (pp_type) {
    case 0:
      return "Str";
    case 1:
      return "Pp";
    case 2:
      return "Pp";
  }
}

export namespace CoqLspClientConfig {
  export function create(wsConfig: any): CoqLspClientConfig {
    let obj: CoqLspClientConfig = {
      show_goals_on: wsConfig.show_goals_on,
      pp_format: pp_type_to_pp_format(wsConfig.pp_type),
      check_on_scroll: wsConfig.check_on_scroll,
    };
    return obj;
  }
}

export namespace CoqSelector {
  // All Coq files, regardless of the scheme.
  export const all: TextDocumentFilter[] = [
    { language: "coq" },
    { language: "markdown", pattern: "**/*.mv" },
    { language: "latex", pattern: "**/*.lv" },
    { language: "latex", pattern: "**/*.v.tex" },
  ];

  // Local Coq files, suitable for interaction with a local server
  export const local: TextDocumentFilter[] = all.map((selector) => {
    return { ...selector, scheme: "file" };
  });

  // VSCode Live Share URIs
  export const vsls: TextDocumentFilter[] = all.map((selector) => {
    return { ...selector, scheme: "vsls" };
  });

  // Virtual workspaces such as github.dev
  export const virtual: TextDocumentFilter[] = all.map((selector) => {
    return { ...selector, scheme: "vscode-vfs" };
  });

  // Files that are owned by our server, local + virtual
  export const owned: TextDocumentFilter[] = local.concat(virtual);
}
