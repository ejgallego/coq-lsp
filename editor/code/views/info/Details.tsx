import { PropsWithChildren } from "react";

export type DetailsP = PropsWithChildren<{
  summary: React.ReactNode;
  open?: boolean;
}>;

export function Details({ summary, open, children }: DetailsP) {
  return (
    <details style={{ marginBottom: "1ex" }} open={open ?? true}>
      <summary>{summary}</summary>
      <div style={{ marginLeft: "1ex", marginBottom: "1ex" }}>{children}</div>
    </details>
  );
}
