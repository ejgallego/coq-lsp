import { Loc } from "../../lib/types";

export type LocP = { loc?: Loc };

// Note, this is for display, so we need to adjust for both lines and
// columns to start at 1, hence the + 1
export function Loc({ loc }: LocP) {
  if (!loc) return null;
  let l1 = loc.line_nb;
  let c1 = loc.bp - loc.bol_pos + 1;
  let l2 = loc.line_nb_last;
  let c2 = loc.ep - loc.bol_pos_last + 1;

  return <span>{`l:${l1},c:${c1}--l:${l2},c:${c2}`}</span>;
}
