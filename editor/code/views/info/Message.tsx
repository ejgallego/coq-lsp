// import objectHash from "object-hash";
import { useLayoutEffect, useRef } from "react";
import { Message } from "../../lib/types";
import { PpString } from "../../lib/types";
import { CoqPp } from "./CoqPp";
import { FormatPrettyPrint } from "../../lib/format-pprint/js/main";
import $ from "jquery";

export function Message({
  key,
  message,
}: {
  key: React.Key;
  message: PpString | Message<PpString>;
}) {
  const ref: React.LegacyRef<HTMLLIElement> | null = useRef(null);
  useLayoutEffect(() => {
    if (ref.current) {
      FormatPrettyPrint.adjustBreaks($(ref.current));
    }
  });

  let text =
    typeof message === "string"
      ? message
      : typeof message === "object" && "text" in message
      ? message.text
      : message;

  return (
    <li key={key} className={"coq-message"} ref={ref}>
      <CoqPp content={text} inline={true} />
    </li>
  );
}
