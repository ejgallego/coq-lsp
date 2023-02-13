import objectHash from "object-hash";
import { ReactEventHandler, useEffect, useRef, useState } from "react";
import { Hyp, Goal, GoalConfig } from "../../lib/types";
import { CoqPp } from "./CoqPp";
import { Details } from "./Details";

import "./media/goals.css";

// to replace by CoqPp | string
type CoqPp = string;
type CoqId = string;

function Hyp({ hyp: { names, def, ty } }: { hyp: Hyp<CoqPp> }) {
  let className = "coq-hypothesis" + (def ? " coq-has-def" : "");
  let mkLabel = (id: CoqId) => <label>{id}</label>;
  let mkdef = (pp?: CoqPp) =>
    pp ? (
      <span className="def">
        <CoqPp content={pp} inline={true} />
      </span>
    ) : null;

  return (
    <div className={className}>
      {names.map(mkLabel)}
      {mkdef(def)}
      <div>
        <CoqPp content={ty} inline={true} />
      </div>
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

type GoalP = { goal: Goal<string>; idx: number; open: boolean };

function Goal({ goal, idx, open }: GoalP) {
  const className = open ? undefined : "aside";

  return (
    <div className="coq-goal-env">
      <Details summary={`Goal (${idx})`} open={open}>
        <div style={{ paddingTop: "1ex" }} />
        <Hyps hyps={goal.hyps} />
        <hr />
      </Details>
      <div style={{ marginLeft: "1ex" }} className={className}>
        <CoqPp content={goal.ty} inline={false} />
      </div>
    </div>
  );
}

type GoalsListP = {
  goals: Goal<string>[];
  header: string;
  show_on_empty: boolean;
  open: boolean;
  bullet_msg?: string;
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
            {bullet_msg ? <p className="aside">{bullet_msg}</p> : null}
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
type StackSummaryP = { idx: number; stack: [Goal<CoqPp>[], Goal<CoqPp>[]][] };

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
        open={true}
        show_on_empty={false}
      />
      <div style={{ marginLeft: "0.5ex" }}>
        <StackGoals idx={idx + 1} stack={stack} />
      </div>
    </div>
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
