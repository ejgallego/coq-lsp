import { PropsWithChildren } from "react";
import { GoalRequest } from "../../lib/types";
import { Details } from "./Details";

export type FileInfoParams = PropsWithChildren<GoalRequest>;
export function FileInfo({ textDocument, position, children }: FileInfoParams) {
  let uri = textDocument.uri.split("/").at(-1);
  let line = position.line + 1;
  let character = position.character + 1;
  let summary = (
    <span>
      {uri}:{line}:{character}
    </span>
  );

  return <Details summary={summary}>{children}</Details>;
}
