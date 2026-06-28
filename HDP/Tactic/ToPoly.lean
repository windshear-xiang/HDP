import HDP.Data.Poly
import HDP.Tactic.State
import Lean.Meta.AppBuilder

/-!
Parse Lean `Expr` → internal `P[F]` polynomial

TODO: Currently we just take everything as `Rat` blindly
-/

open Lean Meta
open Lean.Grind (Field)

namespace HDP

open HDP.Data

/-- Parse an `Expr` into `P[F]` polynomial.
    Atoms are automatically registered / looked up in `HdpState`. -/
partial def asPoly (e : Expr) : HdpM P[Rat] := do
  if let some n := e.int? then
    return Poly.ofMTerm (n : Int)
  match_expr e with
  | HAdd.hAdd _ _ _ _ a b =>
    pure ((← asPoly a) + (← asPoly b))
  | HSub.hSub _ _ _ _ a b =>
    pure ((← asPoly a) - (← asPoly b))
  | HMul.hMul _ _ _ _ a b =>
    pure ((← asPoly a) * (← asPoly b))
  | Neg.neg _ _ a =>
    pure (-(← asPoly a))
  | HPow.hPow _ _ _ _ base exp =>
    match exp.nat? with
    | some n => pure ((← asPoly base) ^ n)
    | none =>
      let i ← HdpState.addAtom e
      return Poly.ofMonomial (Monomial.eᵢ i)
  | _ =>
    let i ← HdpState.addAtom e
    return Poly.ofMonomial (Monomial.eᵢ i)

end HDP
