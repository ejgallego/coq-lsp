import { PropsWithChildren, DetailsHTMLAttributes } from "react";

export type DetailsP = PropsWithChildren<
  {
    summary: React.ReactNode;
  } & DetailsHTMLAttributes<HTMLDetailsElement>
>;

export function Details({ summary, children, open, ...rest }: DetailsP) {
  return (
    <details style={{ marginBottom: "1ex" }} open={open ?? true} {...rest}>
      <summary>{summary}</summary>
      <div style={{ marginLeft: "1ex", marginBottom: "1ex" }}>{children}</div>
    </details>
  );
}
