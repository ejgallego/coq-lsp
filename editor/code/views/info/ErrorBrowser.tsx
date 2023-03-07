import { PpString } from "../../lib/types";
import { CoqPp } from "./CoqPp";

export type ErrorBrowserParams = { error: PpString };

export function ErrorBrowser({ error }: ErrorBrowserParams) {
  return (
    <>
      <header>Errors:</header>
      <CoqPp content={error} inline={true} />;
    </>
  );
}
