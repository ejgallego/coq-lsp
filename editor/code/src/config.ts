import { ExtensionContext, workspace } from "vscode";

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
}

export namespace CoqLspClientConfig {
  export function create(wsConfig: any): CoqLspClientConfig {
    let obj: CoqLspClientConfig = { show_goals_on: wsConfig.show_goals_on };
    return obj;
  }
}
