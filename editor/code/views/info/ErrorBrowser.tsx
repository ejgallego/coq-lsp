import { CoqPp } from "./CoqPp";
import { Details } from "./Details";

export type ErrorBrowserParams = { error?: string };

export function ErrorBrowser({ error }: ErrorBrowserParams) {
  if (!error) return null;

  return (
    <Details summary={"Error Browser"}>
      <CoqPp content={error} inline={false} />
    </Details>
  );
}
