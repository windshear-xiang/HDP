import Lean.Elab.Tactic

import HDP.Tactic.Normalize
import HDP.Tactic.ToExpr
import HDP.Tactic.ToPoly
import HDP.Data.Buchberger

open Lean Meta Elab Tactic
open Lean.Grind (Field)

namespace HDP

open HDP.Data

def hdpTactic : TacticM Unit := do
  let g₀ ← getMainGoal
  let g ← g₀.withContext do processGoal g₀

  let goalType ← g.getType
  logInfo m!"normalized goal = {goalType}"

  g.withContext do
    let hyps ← getLocalHyps
    let mut atoms : Array Expr := #[]
    let mut polys : Array P[Rat] := #[]

    -- Parse all hypotheses into polynomials
    for h in hyps do
      (atoms, polys) ← ProcessFact atoms polys h
    logInfo m!"atoms in hyps = {atoms}"
    logInfo m!"polys in hyps = {polys}"

    -- Parse goal into polynomial
    let some (mulPoly, targetPoly, atomsFinal) ← (do
      match_expr goalType with
      | Exists _α body =>
        lambdaTelescope body fun eFvars body' => do
          let #[_e] := eFvars | return none
          match_expr body' with
          | Eq _α lhs rhs =>
            match_expr rhs with
            | HMul.hMul _ _ _ _ a _eVar =>
              let (atoms1, ap) ← asPoly atoms  a
              let (atoms2, bp) ← asPoly atoms1 lhs
              return some (ap, bp, atoms2)
            | _ => return none
          | _ => return none
      | _ => return none) | throwError "goal not of form ∃ e, b = a * e"
    atoms := atomsFinal
    logInfo m!"goal of form ∃ e, {mulPoly} * e = {targetPoly}"
    logInfo m!"atoms (final) = {atoms}"

    polys := polys.push mulPoly
    logInfo m!"Check whether {targetPoly} in Ideal {polys}"

    let some w := Buchberger.idealMembership targetPoly polys
      | throwError "ideal membership failed: target not in ideal"
    logInfo m!"witness poly = {w}"

    let some cofactor := w[w.size - 1]?
      | throwError "empty witness array"

    let witnessExpr ← polyToExpr cofactor atoms
    logInfo m!"witness expr = {witnessExpr}"

    evalTactic (← `(tactic| refine ⟨?w, ?eq⟩))
    match ← getGoals with
    | [wMVar, eqMVar] =>
      wMVar.assign witnessExpr
      setGoals [eqMVar]
      try
        evalTactic (← `(tactic| grind))
      catch err => throwError "grind failed with {err.toMessageData}"
    | _ => throwError "unexpected goal shape after refine"

end HDP
