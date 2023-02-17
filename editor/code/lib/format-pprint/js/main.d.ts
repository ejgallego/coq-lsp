import { Pp } from "../../types";

export class FormatPrettyPrint {
  static pp2DOM(pp: Pp, topBox: "vertical" | "horizontal"): JQuery<HTMLElement>;
  static adjustBreaks(pp: JQuery<HTMLElement>): void;
}
