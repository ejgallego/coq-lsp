import { PpString } from "../../lib/types";
import { CoqPp } from "./CoqPp";
import { Details } from "./Details";

export type ErrorBrowserParams = { error?: PpString };

export function ErrorBrowser({ error }: ErrorBrowserParams) {
  if (!error) return null;

  return (
    <Details summary={"Error Browser"}>
      <CoqPp content={error} inline={true} />
    </Details>
  );
}
