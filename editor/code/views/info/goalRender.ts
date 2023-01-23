import { Hyp, Goal, GoalAnswer, GoalConfig } from "../../lib/types";

function htmlOfCoqInline(t: string) {
  return `<code>${t}</code>`;
}

function htmlOfCoqBlock(t: string) {
  return `<pre>${t}</pre>`;
}

function htmlOfHyp(hyp: Hyp) {
  let hypBody =
    `<label class="hname">${hyp.names}</label>` +
    `<label class="sep"> : </label>` +
    `<span class="htype">${htmlOfCoqInline(hyp.ty)}</span><br/>`;

  return `<div class="hypothesis"> ${hypBody} </div>`;
}

function detailsOfList(
  open: boolean,
  elems: any[],
  summary: string,
  inner: string
) {
  let detailsStatus = elems.length > 0 && open ? "open" : "closed";
  return `
    <details ${detailsStatus}>
        <summary>${summary} [${elems.length}]</summary>
        <div style="margin-left: 1ex;"> ${inner} </div>
    </details>`;
}

function htmlOfGoal(goal: Goal, idx: number) {
  let hyps = goal.hyps.map(htmlOfHyp).join(" ");
  let goalBody = `<div class="pp_goals"> <span class="goal">${htmlOfCoqBlock(
    goal.ty
  )}</span></div>`;
  let summary = `<summary>Goal ${idx}</summary>`;
  return (
    `<details ${idx == 0 ? "open" : "closed"}> ${summary}` +
    `<div class="goalDiv">${hyps} <hr/> ${goalBody} </div>` +
    `</details>`
  );
}

// returns the HTML code of goals environment
function htmlOfGoals(goals: Goal[]) {
  if (goals.length == 0) return "No goals";
  else return goals.map(htmlOfGoal).join(" ");
}

function detailsOfGoalList(open: boolean, name: string, goals: Goal[]) {
  let goalsInner: string = htmlOfGoals(goals);
  return detailsOfList(open, goals, name, goalsInner);
}

function buildGoalsContent(g: GoalConfig) {
  let goalsBody = detailsOfGoalList(true, "Goals", g.goals);
  let shelfBody =
    g.shelf.length > 0 ? detailsOfGoalList(false, "Shelf", g.shelf) : "";
  let givenBody =
    g.given_up.length > 0
      ? detailsOfGoalList(false, "Given Up", g.given_up)
      : "";
  return `
      ${goalsBody}
      <div style="margin-left: 0.5ex">
        ${shelfBody}
        ${givenBody}
      </div>`;
}

// Returns the HTML code of the panel and the inset ccontent
export function buildInfoContent(goals: GoalAnswer) {
  // get the HTML code of goals environment
  let goalsBody = goals.goals ? buildGoalsContent(goals.goals) : "";
  let messageBody = detailsOfList(
    true,
    goals.messages,
    "Messages",
    goals.messages.map(htmlOfCoqBlock).join(" ")
  );

  let errorBody = goals.error
    ? detailsOfList(true, [0], "Error Browser", htmlOfCoqBlock(goals.error))
    : "";
  let uri = goals.textDocument.uri.split("/").at(-1);
  let line = goals.position.line + 1;
  let character = goals.position.character + 1;

  // Use #FA8072 color too?
  return `<details open>
            <summary>${uri}:${line}:${character}</summary>
            <div class="goals_env" style="margin-left: 1ex; margin-top: 1ex; margin-bottom: 1ex;">
              ${goalsBody}
            </div>
            <div style="margin-left: 1ex; margin-bottom: 1ex;">
              ${messageBody}
            </div>
            <div style="margin-left: 1ex; margin-bottom: 1ex;">
              ${errorBody}
            </div>
          </details>`;
}
