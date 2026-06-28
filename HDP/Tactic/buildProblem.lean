import HDP.Data.Poly
import HDP.Data.LinearForm
import HDP.Tactic.ToPoly
import HDP.Tactic.State

import Lean.Elab.Tactic

open Lean Meta
open Lean.Grind (Field)

namespace HDP

open HDP.Data

private partial def processFactAux (h : Expr) : HdpM Unit := do
  let t ← inferType h
  match_expr ← whnf t with
  | Eq α lhs rhs =>
    if α.isConstOf ``Int then
      let plhs ← asPoly lhs
      let prhs ← asPoly rhs
      let p := plhs - prhs
      HdpState.addPoly p
      trace[hdp.build.hyps.hyp] "{p}"
  | And _ _ =>
    processFactAux (← mkAppM ``And.left #[h])
    processFactAux (← mkAppM ``And.right #[h])
  | Exists _ _ =>
    processFactAux (← mkAppM ``Exists.choose_spec #[h])
  | _ =>
    pure ()

/-- Process a single hypothesis, recording its polynomial contribution to `HdpState`. -/
def processFact (h : Expr) : HdpM Unit := do
  let t ← inferType h
  withTraceNode `hdp.build.hyps.hyp (msg := fun _ => pure m!"{h} : {t}") do
    processFactAux h

/--
  Collecting all prefix existential quantifier, and adding these variables in to `HdpState.Atoms`.

  Return the index list of those variables in `Atoms` and the body part left.
-/
partial def collectExists (goalType : Expr) (ys : Array Nat) :
    HdpM (Array Nat × Expr) := do
  let goalType ← whnf goalType
  match_expr goalType with
  | Exists _α body =>
    lambdaTelescope body fun yFVars body' => do
      let #[y] := yFVars
        | throwError "parseGoal: expected one binder under Exists, got {yFVars.size}"
      let yAtomIdx ← HdpState.addAtom y
      collectExists body' (ys.push yAtomIdx)
  | _ =>
    return (ys, goalType)

partial def parseToLFs (e : Expr) (ys : Array Nat) : HdpM (Array (LinearForm Rat)) := do
  let e ← whnf e
  match_expr e with
  | And e₁ e₂ =>
    let lf₁ ← parseToLFs e₁ ys
    let lf₂ ← parseToLFs e₂ ys
    return lf₁ ++ lf₂
  | Eq α lhs rhs =>
    let α ← whnf α
    if !α.isConstOf ``Int then
      throwError "parseGoal: expected Int equation only, got {e} : {α}"

    let plhs ← asPoly lhs
    let prhs ← asPoly rhs
    match (Poly.linearizeIn (plhs - prhs) ys) with
    | some lf => return #[lf]
    | none =>
      throwError "parseGoal: goal equation is nonlinear in its existential witnesses"
  | _ =>
    throwError "parseGoal: expected existential goal ending in an equation, got {e}"

/--
  Parse the normalized goal of form `∃ y₁ ... yₙ, complexEq ∧ ... ∧ complexEq`

  into an Array of `LinearForm`s
-/
def parseGoal (goalType : Expr) : HdpM (Nat × Array (LinearForm Rat)) := do
  let (ys, body) ← collectExists goalType #[]
  if ys.isEmpty then
    throwError "parseGoal: goal has no existential quantifiers"

  let lfs ← parseToLFs body ys
  return (ys.size, lfs)

/--
  Given an Array of LinearForms:
    ```
    p₁₁ * y₁ + ... + p₁ₙ * yₙ = a₁
                  ∧
                  ⋮
                  ∧
    pₖ₁ * y₁ + ... + pₖₙ * yₙ = aₖ
    ```
  Convert it into Ideal membership problem:
    ```
    target = a₁*u₁ + ... + aₖ*uₖ
    generators =
      facts...,
      p₁₁*u₁ + ... + pₖ₁*uₖ,
      ...
      p₁ₙ*u₁ + ... + pₖₙ*uₖ
    ```
  with new auxiliary variables `u₁, ..., uₖ`
-/
def buildIdealProblem (lfs : Array (LinearForm Rat)) : HdpM (Array Nat × P[Rat] × Array P[Rat]) := do
  let some lf₀ := lfs[0]?
    | throwError "buildIdealProblem: expected at least one linear form"
  let n := lf₀.size

  for lf in lfs do
    if lf.size != n then
      throwError "buildIdealProblem: inconsistent number of existential witnesses, expected {n}, got {lf.size} in {lf}"

  let us ← lfs.mapIdxM fun i _ => do
    let uExpr ← mkFreshExprMVar (some (mkConst ``Int)) .natural (Name.mkSimple s!"aux_{i}")
    HdpState.addAtom uExpr

  let uPoly (i : Nat) : P[Rat] :=
    Poly.ofMonomial (Monomial.eᵢ us[i]!)

  let targetPoly :=
    lfs.mapIdx (fun i lf => lf.const * uPoly i)
      |>.foldl (init := 0) (fun acc p => acc + p)
      |> Poly.canonicalize

  let idealGenPoly :=
    (List.range n).foldl
      (init := #[])
      (fun gens j =>
        let gen :=
          lfs.mapIdx (fun i lf => lf.coeffs[j]! * uPoly i)
            |>.foldl (init := 0) (fun acc p => acc + p)
            |> Poly.canonicalize
        gens.push gen)

  return (us, targetPoly, idealGenPoly)

end HDP
