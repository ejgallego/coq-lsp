// import objectHash from "object-hash";
import { Message } from "../../lib/types";
import { PpString } from "../../lib/types";
import { CoqPp } from "./CoqPp";

export function Message({
  key,
  message,
}: {
  key: React.Key;
  message: PpString | Message<PpString>;
}) {
  let text =
    typeof message === "string"
      ? message
      : typeof message === "object" && "text" in message
      ? message.text
      : message;

  return (
    <li key={key}>
      <CoqPp content={text} inline={true} />
    </li>
  );
}
