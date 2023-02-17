import { PropsWithChildren, DetailsHTMLAttributes } from "react";

export type DetailsP = PropsWithChildren<
  {
    summary: React.ReactNode;
  } & DetailsHTMLAttributes<HTMLDetailsElement>
>;

export function Details({ summary, children, open, ...rest }: DetailsP) {
  return (
    <details open={open ?? true} {...rest}>
      <summary>{summary}</summary>
      <div style={{ paddingLeft: "1ex", paddingBottom: "1ex" }}>{children}</div>
    </details>
  );
}
