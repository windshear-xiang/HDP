import Lean.Elab.Tactic

import HDP.Data.Buchberger
import HDP.Data.LinearForm
import HDP.Tactic.ToExpr
import HDP.Tactic.ToPoly
import HDP.Tactic.Normalize
import HDP.Tactic.buildProblem

open Lean Meta Elab Tactic
open Lean.Grind (Field)

namespace HDP

open HDP.Data

def hdpSolveSingle : TacticM Unit := do
  withTraceNode `hdp (msg := fun _ => pure m!"Solving branch") do
    -- Print raw goal if needed
    withTraceNode `hdp.goal (msg := fun _ => pure m!"Current goal") do
      trace[hdp.goal] m!"{← getMainGoal}"

    -- Normalize & rewrite current goal and all hypotheses.
    let gNorm ← withTraceNode `hdp.normalize (msg := fun _ => pure "Normalizing goal and hypothesis") do
      normalizeGHs
      getMainGoal

    let (ws, hdpState) ← gNorm.withContext do
      (do
        withTraceNode `hdp.build (msg := fun _ => pure "Building ideal membership problem") do

          -- Record all hypotheses as polynomials in HdpState
          withTraceNode `hdp.build.hyps (msg := fun _ => pure "Polynomials from hypotheses") do
            let hyps ← getLocalHyps
            hyps.forM processFact

          -- Parse goal into polynomial linear forms
          let (n_exists, lfs) ← parseGoal (← gNorm.getType)
          trace[hdp.build.lin_goal] "∃ {" ".intercalate ((List.range n_exists).map (s!"y{· + 1}"))},\n        {"\n     ∧ ".intercalate (lfs.toList.map toString)}"

          -- Build ideal membership problem
          let (us, targetPoly, idealGenPolys) ← buildIdealProblem lfs
          let st ← getThe HdpState
          trace[hdp.build.atoms] "{st.atoms}"
          trace[hdp.build.aux_var] "{us.map (s!"x{· + 1}")}"
          let ps := st.polys ++ idealGenPolys
          trace[hdp.build.problem] "({targetPoly}) ∈? Ideal {ps}"

          -- Check ideal membership
          let some cofs := Buchberger.idealMembership targetPoly ps
            | throwError "Target Polynomial not in ideal"
          trace[hdp.build.cofactors] "{cofs}"
          let ws := ((cofs.drop (cofs.size - n_exists)).map (Poly.constantPartIn · us))
          trace[hdp.build.witnesses] "{ws}"
          return ws
      : HdpM (Array (P[Rat]))).run {}

    -- Proof synthesis
    gNorm.withContext do
      withTraceNode `hdp.proof (msg := fun _ => pure "Constructing proof") do
        for w in ws do
          let witnessExpr ← polyToExpr w hdpState.atoms
          trace[hdp.proof.witness_expr] "{witnessExpr}"

          evalTactic (← `(tactic| refine ⟨?_, ?_⟩))
          match ← getGoals with
          | [wMVar, restMVar] =>
            wMVar.assign witnessExpr
            setGoals [restMVar]
          | other =>
            throwError "Unexpected goal shape after refining existential witness: {other}"

        match ← getGoals with
        | [eqMVar] =>
          trace[hdp.proof.eqs] "{← eqMVar.getType}"
          try
            evalTactic (← `(tactic| grind))
          catch e =>
            throwError "Tactic `grind` failed with {e.toMessageData}"
          let goalsAfter ← getUnsolvedGoals
          unless goalsAfter.isEmpty do
            throwError "Tactic `grind` left unsolved goals: {goalsAfter}"
        | other =>
          throwError "Unexpected goal shape after assign existential witness: {other}"

partial def hdpTactic : TacticM Unit := do
  let gType ← whnf (← getMainTarget)
  match_expr gType with
  | And _ _ =>
    evalTactic (← `(tactic| refine And.intro ?_ ?_))
    for g' in ← getUnsolvedGoals do
      setGoals [g']
      hdpTactic
  | Iff _ _ =>
    evalTactic (← `(tactic| refine Iff.intro ?_ ?_))
    for g' in ← getUnsolvedGoals do
      setGoals [g']
      hdpTactic
  | _ =>
    if gType.isForall then
      -- Intro implication antecedent / forall binder
      evalTactic (← `(tactic| intro))
      hdpTactic
    else
      focus hdpSolveSingle

end HDP
