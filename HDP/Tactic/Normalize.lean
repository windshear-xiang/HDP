import HDP.Data.Poly
import HDP.Tactic.ToPoly
import HDP.Tactic.State
import HDP.Tactic.bezout

import Lean.Elab.Tactic

open Lean Meta Elab Tactic
open Lean.Grind (Field)

namespace HDP

open HDP.Data

theorem dvd_iff_exists {a b : Int} : a ∣ b ↔ ∃ c, b = a * c := ⟨id, id⟩

theorem emod_eq_zero_iff_dvd {a b : Int} : b % a = 0 ↔ a ∣ b := Int.dvd_iff_emod_eq_zero.symm

theorem emod_eq_iff_dvd {a b m : Int} : a % m = b % m ↔ m ∣ a - b := by
  constructor
  · intro h
    rw [Int.dvd_iff_emod_eq_zero]
    exact Int.emod_eq_emod_iff_emod_sub_eq_zero.mp h
  · intro h
    rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
    exact emod_eq_zero_iff_dvd.mpr h

theorem exists_right {p : α → Prop} {q : Prop} :
    ((∃ x, p x) ∧ q) ↔ ∃ x, p x ∧ q := exists_and_right.symm

theorem exists_left {p : Prop} {q : α → Prop} :
    (p ∧ ∃ x, q x) ↔ ∃ x, p ∧ q x := exists_and_left.symm



theorem emod_note {m n : Int} : ∃ q, m - m % n = n * q := Int.dvd_self_sub_emod

theorem gcd_note {m n : Int} :
    (∃ x, m = (Int.gcd m n : Int) * x)
    ∧ (∃ y, n = (Int.gcd m n : Int) *y)
    ∧ (∃ u v, m * u + n * v = (Int.gcd m n : Int)) :=
  ⟨ (Int.gcd_dvd_left m n), (Int.gcd_dvd_right m n), bezout_gcd m n ⟩

def neqSimpWrapper (a b t : Int) : Prop := a * t = b * t

theorem remove_wrapper {a b t : Int} : neqSimpWrapper a b t ↔ a * t = b * t := Iff.rfl

theorem neq_note {l r a b : Int}
    (hneq : l ≠ r) :
    (a = b) ↔ neqSimpWrapper a b (l - r) := by
  have hnz : l - r ≠ 0 := by
    intro hlr; rw [Int.sub_eq_zero] at hlr
    exact hneq hlr
  exact (Int.mul_eq_mul_right_iff hnz).symm


/-- Record all `mod`, `gcd` definitions appear in Expr `e` -/
def recordDefIn (e : Expr) : NormM Unit := do
  match_expr e with
  | HMod.hMod _ _ _ _ m n =>
    if e.hasLooseBVars then
      trace[hdp.normalize.mod] "skip loose bound {e}"
    else
      trace[hdp.normalize.mod] "{e}"
      NormState.addModAtom m n
  | Int.gcd m n =>
    if e.hasLooseBVars then
      trace[hdp.normalize.gcd] "skip loose bound {e}"
    else
      trace[hdp.normalize.gcd] "{e}"
      NormState.addGcdAtom m n
  | _ => return

def recordIfNeqHyp (decl : LocalDecl) : NormM Unit := do
  let t ← whnf decl.type
  unless t.isForall && t.bindingBody!.isConstOf ``False do
    return
  let_expr Eq α _ _ ← t.bindingDomain! | return
  if α.isConstOf ``Int then
    let userName := decl.userName
    trace[hdp.normalize.neq] "{userName} : {decl.type}"
    NormState.addneqHypName userName

/--
  Check if the goal is indeed of form `∃ y₁ ... yₙ, complexEq ∧ ... ∧ complexEq`

  Return `Unit` if it pass the check; Throw an error if it not.
-/
partial def checkGoalNormalized (gType : Expr) : TacticM Unit := do
  match_expr ← whnf gType with
  | And e₁ e₂ => do
    checkGoalNormalized e₁
    checkGoalNormalized e₂
    return
  | Eq α _ _ => do
    if !α.isConstOf ``Int then
      throwError "Expected Int equation in goal only, got {α} at {gType}"
    return
  | Exists α body => do
    if !α.isConstOf ``Int then
      throwError "Expected Int existential variable in goal only, got {α} at {gType}"
    lambdaTelescope body fun xs body' => do
      if xs.size != 1 then
        throwError "Expected one binder under Exists, got {xs.size}"
      checkGoalNormalized body'
  | _ => throwError "Unsupported goal shape {gType}"

/--
  Normalize current goal and Hyps into the form `∃ y₁ ... yₙ, complexEq ∧ ... ∧ complexEq`
-/
def normalizeGHs : TacticM Unit := do
  let g₀ ← getMainGoal

  -- simplify dvd, emod, and nested exists in goal and all hypotheses
  g₀.withContext do
    discard <| tryTactic do
      evalTactic (← `(tactic|
        simp only [
          HDP.dvd_iff_exists,
          HDP.emod_eq_zero_iff_dvd,
          HDP.emod_eq_iff_dvd,
          HDP.exists_right,
          HDP.exists_left
        ] at *))

  let [g₁] ← getUnsolvedGoals
    | throwError m!"Expected 1 goal after simp, got {(← getUnsolvedGoals).length}"

  let g₁Type ← g₁.getType
  checkGoalNormalized (g₁Type)

  -- Record all mod, gcd, and neq hyp
  let (_, normState) <-
    g₁.withContext do
      (do
        let lctx ← getLCtx
        lctx.forM fun decl => do
          if decl.isImplementationDetail then return
          Expr.forEach decl.type recordDefIn
          recordIfNeqHyp decl
        Expr.forEach g₁Type recordDefIn
      : NormM Unit).run {}

  -- Add auxilary note hypothesis for all mod, gcd
  let g₂ <- g₁.withContext do
    normState.modAtoms.foldlM
      (fun g (m, n) => do
      let proof := mkApp2 (mkConst ``emod_note) m n
      return (← g.note (Name.mkSimple s!"mod_{← ppExpr m}_{← ppExpr n}") proof).snd
      ) (
    ← normState.gcdAtoms.foldlM
      (fun g (m, n) => do
      let proof := mkApp2 (mkConst ``gcd_note) m n
      return (← g.note (Name.mkSimple s!"gcd_{← ppExpr m}_{← ppExpr n}") proof).snd
      )
    g₁ )
  replaceMainGoal [g₂]

  -- transform goal for all neqs
  g₂.withContext do
    normState.neqHypNames.forM fun hneqName => do
      let hneq_stx := mkIdent hneqName
      evalTactic (← `(tactic|
        simp only [(HDP.neq_note $hneq_stx:term)];
        simp only [remove_wrapper]
      ))

  let [g₃] ← getUnsolvedGoals
    | throwError m!"Expected 1 goal after transform, got {(← getUnsolvedGoals).length}"

  g₃.withContext do
    withTraceNode `hdp.normalize.goal (msg := fun _ => pure m!"Normalized goal") do
      trace[hdp.normalize.goal] m!"{g₃}"

  return

end HDP
