import objectHash from "object-hash";
import { CoqPp } from "./CoqPp";

export function Message({ message }: { message: string }) {
  let key = objectHash(message);
  return (
    <li key={key}>
      <CoqPp content={message} inline={true} />
    </li>
  );
}
