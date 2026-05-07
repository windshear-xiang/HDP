import HDP.Data.Poly
import HDP.Tactic.ToPoly

import Lean.Elab.Tactic


/-!
Preprocess complex number-theory expressions, normalize them into pure polynomial equations.
-/

open Lean Meta
open Lean.Grind (Field)

namespace HDP

open HDP.Data

theorem Int.exists_of_dvd {a b : Int} : a ∣ b → ∃ c, b = a * c := id

theorem Int.dvd_of_exists {a b : Int} : (∃ c, b = a * c) → (a ∣ b) := id

partial def ProcessFact (atoms : Array Expr) (polys : Array P[Rat])
    (h : Expr) : MetaM (Array Expr × Array P[Rat]) := do
  let t ← inferType h -- TODO: whnfR here?
  match_expr t with
  | Eq α lhs rhs =>
    if α.isConstOf ``Int then
      -- parse `lhs = rhs` as polynomial (lhs - rhs)
      let (atoms, plhs) ← asPoly atoms lhs
      let (atoms, prhs) ← asPoly atoms rhs
      return (atoms, polys.push (plhs - prhs))
    else
      return (atoms, polys)
  | Dvd.dvd α _ a b =>
    if α.isConstOf ``Int then
      ProcessFact atoms polys
        (mkApp3 (.const ``HDP.Int.exists_of_dvd []) a b h)
    else
      return (atoms, polys)
  | Exists α P =>
    let lvl ← getLevel α
    ProcessFact atoms polys
      (mkApp3 (.const ``Exists.choose_spec [lvl]) α P h)
  | _ => return (atoms, polys)

partial def processGoal (g : MVarId) : MetaM MVarId := do
  g.withContext do
    let t ← g.getType
    match_expr t with
    | Dvd.dvd α _ a b =>
      if α.isConstOf ``Int then
        match ← g.apply (mkApp2 (.const ``HDP.Int.dvd_of_exists []) a b) with
        | [g'] => return g'
        | _ => throwError "converting dvd expression {t} in goal failed."
      else
        return g
    | _ => return g

end HDP
