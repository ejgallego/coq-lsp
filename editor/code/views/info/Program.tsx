import objectHash from "object-hash";
import { Id, OblsView, ProgramInfo } from "../../lib/types";
import { Details } from "./Details";
import { Loc } from "./Loc";

type ProgramEntryP = { pentry: [Id, OblsView] };

function ProgramEntry({ pentry }: ProgramEntryP) {
  let [pname, pobls] = pentry;

  let total = pobls.obligations.length;
  let summary = (
    <span>
      {pname[1]} (remaining: {pobls.remaining}/{total})
    </span>
  );
  return (
    <Details summary={summary}>
      <ul>
        {pobls.obligations.map((value) => {
          let key = objectHash(value);
          return (
            <li key={key}>
              {value.name[1]}: (solved: {value.solved ? "yes" : "pending"}) (loc
              : <Loc loc={value.loc} />)
            </li>
          );
        })}
      </ul>
    </Details>
  );
}

export function Program({ program }: { program?: ProgramInfo }) {
  if (!program || program.length == 0) return null;

  return (
    <Details summary={"Program"}>
      <ProgramEntry pentry={program[0]} />
    </Details>
  );
}
