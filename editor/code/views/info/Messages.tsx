import objectHash from "object-hash";
import { Details } from "./Details";
import { Message } from "./Message";

import "./media/messages.css";

export type MessagesParams = { messages: string[] };

export function Messages({ messages }: MessagesParams) {
  let count = messages.length;
  let open = count > 0;
  return (
    <Details summary={`Messages (${count})`} open={open}>
      <ul className="messageList">
        {messages.map((value, idx) => {
          let key = objectHash(value);
          return <Message key={key} message={value} />;
        })}
      </ul>
    </Details>
  );
}
