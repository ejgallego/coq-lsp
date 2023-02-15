import objectHash from "object-hash";
import { Message } from "../../lib/types";
import { CoqPp } from "./CoqPp";

export function Message({ message }: { message: string | Message<string> }) {
  let key = objectHash(message);
  let text = typeof message === "string" ? message : message.text;
  return (
    <li key={key}>
      <CoqPp content={text} inline={true} />
    </li>
  );
}
