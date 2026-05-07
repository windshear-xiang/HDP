import HDP.Data.Poly
import Lean.Meta.AppBuilder

/-!
Parse Lean `Expr` → internal `P[F]` polynomial

TODO: Currently we just take everything as `Rat` blindly
-/

open Lean Meta
open Lean.Grind (Field)

namespace HDP

open HDP.Data

/--
Check whether an Expr `e` exists in `atoms`.
if `e` is found, return its index;
else just add `e` into `atoms`, return the new `atoms` and `e`'s new index.
-/
def lookupOrInsert (atoms : Array Expr) (e : Expr) : Array Expr × Nat :=
  match atoms.findIdx? (· == e) with
  | some i => (atoms, i)
  | none   => (atoms.push e, atoms.size)

/-- Parse an `Expr` into `P[F]` polynomial, collect atoms along the way. -/
partial def asPoly (atoms : Array Expr) (e : Expr) :
    MetaM (Array Expr × P[Rat]) := do
  if let some n := e.int? then
    return (atoms, Poly.ofMTerm (n : Int))
  match_expr e with
  | HAdd.hAdd _ _ _ _ a b =>
    let (atoms, pa) ← asPoly atoms a
    let (atoms, pb) ← asPoly atoms b
    return (atoms, pa + pb)
  | HSub.hSub _ _ _ _ a b =>
    let (atoms, pa) ← asPoly atoms a
    let (atoms, pb) ← asPoly atoms b
    return (atoms, pa - pb)
  | HMul.hMul _ _ _ _ a b =>
    let (atoms, pa) ← asPoly atoms a
    let (atoms, pb) ← asPoly atoms b
    return (atoms, pa * pb)
  | Neg.neg _ _ a =>
    let (atoms, pa) ← asPoly atoms a
    return (atoms, -pa)
  | _ => -- Everything else just take as atom
    let (atoms, i) := lookupOrInsert atoms e
    return (atoms, Poly.ofMonomial (Monomial.eᵢ i))

end HDP
