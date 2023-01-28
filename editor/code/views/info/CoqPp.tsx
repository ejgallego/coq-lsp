import { PpString } from "../../lib/types";
import { FormatPrettyPrint } from "../../lib/format-pprint/js/main";

import "./media/coqpp.css";

export function CoqPp({
  content,
  inline,
}: {
  content: PpString;
  inline: boolean;
}) {
  if (typeof content == "string") {
    if (inline) {
      return <code style={{ whiteSpace: "pre" }}>{content}</code>;
    } else {
      return <pre className="coqpp">{content}</pre>;
    }
  } else {
    // https://reactjs.org/docs/integrating-with-other-libraries.html
    if (inline) {
      let rendered = FormatPrettyPrint.pp2DOM(content, "horizontal");
      return (
        <div
          style={{ display: "inline" }}
          dangerouslySetInnerHTML={{ __html: rendered.prop("outerHTML") }}
        ></div>
      );
    } else {
      let rendered = FormatPrettyPrint.pp2DOM(content, "vertical");
      return (
        <div
          dangerouslySetInnerHTML={{ __html: rendered.prop("outerHTML") }}
        ></div>
      );
    }
  }
}
