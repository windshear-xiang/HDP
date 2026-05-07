import Lean.ToExpr
import Lean.Meta.AppBuilder
import HDP.Data.Poly

/-!
Convert internal `P[F]` polynomial → Lean `Expr`

TODO: Currently we just translate everything into `Int` blindly
-/

open Lean Meta
open Lean.Grind (Field)

namespace HDP

open HDP.Data

/--
Convert a `Rat` number into an `Expr` of type `Int`.
Will throw error if `den ≠ 1`
-/
def ratCoeffToIntExpr (c : Rat) : MetaM Expr := do
  if c.den != 1 then
    throwError "polyToExpr: non-integer rational coefficient {c} (den = {c.den})"
  return Lean.toExpr c.num

private partial def monomialToIntExprAux (m : Monomial) (atoms : Array Expr) :
    Nat → Option Expr → MetaM (Option Expr)
  | i, acc => do
    if hi : i < m.size then
      let exp := m[i]
      if exp = 0 then
        monomialToIntExprAux m atoms (i + 1) acc
      else
        if i < atoms.size then
          let v := atoms[i]!
          let pw ←
            if exp = 1 then pure v
            else mkAppM ``HPow.hPow #[v, Lean.toExpr exp]
          let acc' ← match acc with
            | none   => pure (some pw)
            | some a => do
              let m ← mkAppM ``HMul.hMul #[a, pw]
              pure (some m)
          monomialToIntExprAux m atoms (i + 1) acc'
        else
          throwError
            "polyToExpr: monomial references atom index {i} (atoms.size = {atoms.size})"
    else
      return acc

/-- Convert a `Monomial` into an `Expr` of type `Int`, with form `xᵢ^eᵢ * …` -/
def monomialToIntExpr (m : Monomial) (atoms : Array Expr) : MetaM (Option Expr) :=
  monomialToIntExprAux m atoms 0 none

/-- Convert a MTerm `M[Rat]` into an `Expr` of type `Int` -/
def mtermToIntExpr (t : M[Rat]) (atoms : Array Expr) : MetaM Expr := do
  let monExpr ← monomialToIntExpr t.monomial atoms
  match monExpr with
  | none =>
    -- constant
    ratCoeffToIntExpr t.coeff
  | some me =>
    if t.coeff = 1 then
      return me
    else if t.coeff = -1 then
      mkAppM ``Neg.neg #[me]
    else
      let cExpr ← ratCoeffToIntExpr t.coeff
      mkAppM ``HMul.hMul #[cExpr, me]

/-- Convert a polynomial `P[Rat]` into an `Expr` of type `Int` -/
def polyToExpr (p : P[Rat]) (atoms : Array Expr) : MetaM Expr := do
  if p.size = 0 then
    return Lean.toExpr (0 : Int)
  let terms ← p.toList.mapM (mtermToIntExpr · atoms)
  match terms with
  | [] => return Lean.toExpr (0 : Int)
  | t :: ts => ts.foldlM (fun acc x => mkAppM ``HAdd.hAdd #[acc, x]) t

end HDP
