import objectHash from "object-hash";
import { Hyp, Goal, GoalConfig, PpString, BoxString } from "../../lib/types";
import { CoqPp } from "./CoqPp";
import { Details } from "./Details";
import { useLayoutEffect, useRef } from "react";
import { FormatPrettyPrint } from "../../lib/format-pprint/js/main";
import $ from "jquery";

import "./media/goals.css";

type CoqId = BoxString;

function Hyp({ hyp: { names, def, ty } }: { hyp: Hyp<BoxString> }) {
  let className = "coq-hypothesis" + (def ? " coq-has-def" : "");
  let mkLabel = (id: CoqId) => <label key={objectHash(id)}>{id}</label>;
  let mkdef = (pp?: BoxString) =>
    pp ? (
      <span className="def">
        <CoqPp content={pp} inline={true} />
      </span>
    ) : null;

  return (
    <div className={className}>
      {names.map(mkLabel)}
      {mkdef(def)}
      <div id="goal-text">
        <CoqPp content={ty} inline={true} />
      </div>
    </div>
  );
}

type HypsP = { hyps: Hyp<BoxString>[] };
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

type GoalP = { goal: Goal<BoxString>; idx: number; open: boolean };

function Goal({ goal, idx, open }: GoalP) {
  const className = open ? undefined : "aside";

  // https://beta.reactjs.org/learn/manipulating-the-dom-with-refs
  const ref: React.LegacyRef<HTMLDivElement> | null = useRef(null);
  const tyRef: React.LegacyRef<HTMLDivElement> | null = useRef(null);
  useLayoutEffect(() => {
    if (ref.current) {
      FormatPrettyPrint.adjustBreaks($(ref.current));
    }
    // See Pfff.v:17160 for tests.
    if (tyRef.current) {
      tyRef.current.scrollIntoView();
    }
  });

  // XXX: We want to add an option for this that can be set interactively
  let show_goal_on_header = false;

  let gtyp = (
    <div style={{ marginLeft: "1ex" }} className={className} ref={tyRef}>
      <div id="goal-text">
        <CoqPp content={goal.ty} inline={false} />
      </div>
    </div>
  );

  return (
    <div className="coq-goal-env" ref={ref}>
      <Details summary={`Goal (${idx})`} open={open}>
        <div style={{ paddingTop: "1ex" }} />
        <Hyps hyps={goal.hyps} />
        <hr />
        {show_goal_on_header ? "" : gtyp}
      </Details>
      {show_goal_on_header ? gtyp : ""}
    </div>
  );
}

type GoalsListP = {
  goals: Goal<BoxString>[];
  header: string;
  show_on_empty: boolean;
  open: boolean;
  bullet_msg?: PpString;
};

function GoalsList({
  goals,
  header,
  open,
  show_on_empty,
  bullet_msg,
}: GoalsListP) {
  let count = goals.length;

  if (count == 0) {
    if (show_on_empty) {
      return (
        <div>
          <p className="no-goals">
            No more goals
            <br />
            {bullet_msg ? (
              <div className="aside">
                <CoqPp content={bullet_msg} inline={true} />
              </div>
            ) : null}
          </p>
        </div>
      );
    } else {
      return null;
    }
  }

  return (
    <Details summary={`${header} (${count})`} open={open}>
      {goals.map((value, idx) => {
        let key = objectHash(value);
        let open = idx === 0 && show_on_empty;
        return <Goal key={key} goal={value} idx={idx + 1} open={open} />;
      })}
    </Details>
  );
}
type StackSummaryP = {
  idx: number;
  stack: [Goal<BoxString>[], Goal<BoxString>[]][];
};

function StackGoals({ idx, stack }: StackSummaryP) {
  let count = stack.length;
  if (count <= idx) return null;

  const [l, r] = stack[idx];
  const goals = l.concat(r);
  let level_indicator =
    idx === 0 ? "the same bullet level" : `the -${idx} bullet level`;

  return (
    <div>
      <GoalsList
        goals={goals}
        header={`Remaining goals at ${level_indicator}`}
        open={idx === 0} // Tweak, should be more configurable
        show_on_empty={false}
      />
      <div style={{ marginLeft: "0.5ex" }}>
        <StackGoals idx={idx + 1} stack={stack} />
      </div>
    </div>
  );
}

type GoalsParams = { goals?: GoalConfig<BoxString, PpString> };

export function Goals({ goals }: GoalsParams) {
  if (!goals) {
    return <p>No goals at this point!</p>;
  }

  return (
    <div className="goal-panel">
      <GoalsList
        goals={goals.goals}
        header={"Goals"}
        show_on_empty={true}
        open={true}
        bullet_msg={goals.bullet}
      />
      <div style={{ marginLeft: "0.5ex" }}>
        <StackGoals idx={0} stack={goals.stack} />
      </div>
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
