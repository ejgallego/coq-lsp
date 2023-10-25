import { PpString } from "../../lib/types";
import { CoqPp } from "./CoqPp";
import { FormatPrettyPrint } from "../../lib/format-pprint/js/main";
import $ from "jquery";
import { useLayoutEffect, useRef } from "react";

export type ErrorBrowserParams = { error: PpString };

export function ErrorBrowser({ error }: ErrorBrowserParams) {
  const ref: React.LegacyRef<HTMLDivElement> | null = useRef(null);
  useLayoutEffect(() => {
    if (ref.current) {
      FormatPrettyPrint.adjustBreaks($(ref.current));
    }
  });

  return (
    <>
      <header>Errors:</header>
      <div className="coq-error" ref={ref}>
        <CoqPp content={error} inline={true} />;
      </div>
    </>
  );
}
