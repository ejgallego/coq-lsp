import { Loc } from "../../lib/types";

export type LocP = { loc?: Loc };
export function Loc({ loc }: LocP) {
  if (!loc) return null;
  let l1 = loc.line_nb + 1;
  let c1 = loc.bp - loc.bol_pos;
  let l2 = loc.line_nb_last + 1;
  let c2 = loc.ep - loc.bol_pos_last;

  return <span>{`l:${l1},c:${c1}--l:${l2},c:${c2}`}</span>;
}
