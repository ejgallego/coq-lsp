interface CoqLspServerDebugConfig {
  cache: boolean;
  send: boolean;
  read: boolean;
  lsp_init: boolean;
  parsing: boolean;
  scan: boolean;
  backtraces: boolean;
  unicode: boolean;
  sched_wakeup: boolean;
  request_delay: boolean;
  mem_stats: boolean;
  gc_quick_stats: boolean;
}

interface CoqLspServerConfig {
  client_version: string;
  mem_stats: boolean;
  gc_quick_stats: boolean;
  eager_diagnostics: boolean;
  ok_diagnostics: boolean;
  goal_after_tactic: boolean;
  show_coq_info_messages: boolean;
  show_notices_as_diagnostics: boolean;
  admit_on_bad_qed: boolean;
  debug: CoqLspServerDebugConfig;
}

export namespace CoqLspServerConfig {
  export function create(client_version: string, wsConfig: any) {
    return {
      client_version: client_version,
      mem_stats: wsConfig.mem_stats,
      gc_quick_stats: wsConfig.gc_quick_stats,
      eager_diagnostics: wsConfig.eager_diagnostics,
      ok_diagnostics: wsConfig.ok_diagnostics,
      goal_after_tactic: wsConfig.goal_after_tactic,
      show_coq_info_messages: wsConfig.show_coq_info_messages,
      show_notices_as_diagnostics: wsConfig.show_notices_as_diagnostics,
      admit_on_bad_qed: wsConfig.admit_on_bad_qed,
      debug: wsConfig.debug,
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
