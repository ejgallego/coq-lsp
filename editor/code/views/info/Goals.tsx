import objectHash from "object-hash";
import { Hyp, Goal, GoalConfig } from "../../lib/types";
import { CoqPp } from "./CoqPp";
import { Details } from "./Details";

function Hyp({ hyp }: { hyp: Hyp<string> }) {
  return (
    <div className="hypothesis">
      <label className="hname">{hyp.names.join(",")}</label>
      <label className="sep"> : </label>
      <span className="htype">
        <CoqPp content={hyp.ty} inline={true} />
      </span>
      <br />
    </div>
  );
}
type HypsP = { hyps: Hyp<string>[] };
function Hyps({ hyps }: HypsP) {
  return (
    <>
      {hyps.map((v) => {
        let key = objectHash(v);
        return <Hyp key={key} hyp={v} />;
      })}
    </>
  );
}

type GoalP = { goal: Goal<string>; idx: number };

function Goal({ goal, idx }: GoalP) {
  let open = idx == 1;
  return (
    <Details summary={`Goal (${idx})`} open={open}>
      <div className="goalDiv">
        <Hyps hyps={goal.hyps} />
        <hr />
        <div className="pp_goals">
          <span className="goal">
            <CoqPp content={goal.ty} inline={false} />
          </span>
        </div>
      </div>
    </Details>
  );
}

type GoalsListP = {
  goals: Goal<string>[];
  header: string;
  show_on_empty: boolean;
  open: boolean;
};

function GoalsList({ goals, header, open, show_on_empty }: GoalsListP) {
  let count = goals.length;

  if (count == 0 && !show_on_empty) return null;

  return (
    <Details summary={`${header} (${count})`} open={open}>
      {goals.map((value, idx) => {
        let key = objectHash(value);
        return <Goal key={key} goal={value} idx={idx + 1} />;
      })}
    </Details>
  );
}

type GoalsParams = { goals?: GoalConfig<string> };

export function Goals({ goals }: GoalsParams) {
  if (!goals) {
    return <p>No goals at this point!</p>;
  }

  return (
    <div className="goalsEnv">
      <GoalsList
        goals={goals.goals}
        header={"Goals"}
        show_on_empty={true}
        open={true}
      />
      <div style={{ marginLeft: "0.5ex" }}>
        <GoalsList
          goals={goals.shelf}
          header={"Shelf"}
          show_on_empty={false}
          open={false}
        />
        <GoalsList
          goals={goals.given_up}
          header={"Given Up"}
          show_on_empty={false}
          open={false}
        />
      </div>
    </div>
  );
}
