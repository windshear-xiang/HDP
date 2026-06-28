import Lean.Meta.AppBuilder
import Lean.Util.Trace
import HDP.Data.Poly

open Lean Meta
open Lean.Grind (Field)

namespace HDP

open HDP.Data

/-- trace classes-/
initialize
  Lean.registerTraceClass `hdp
  Lean.registerTraceClass `hdp.goal                   (inherited := true)
  Lean.registerTraceClass `hdp.normalize              (inherited := true)
  Lean.registerTraceClass `hdp.normalize.goal         (inherited := true)
  Lean.registerTraceClass `hdp.normalize.neq          (inherited := true)
  Lean.registerTraceClass `hdp.normalize.mod          (inherited := true)
  Lean.registerTraceClass `hdp.normalize.gcd          (inherited := true)
  Lean.registerTraceClass `hdp.build                  (inherited := true)
  Lean.registerTraceClass `hdp.build.hyps             (inherited := true)
  Lean.registerTraceClass `hdp.build.hyps.hyp         (inherited := true)
  Lean.registerTraceClass `hdp.build.lin_goal         (inherited := true)
  Lean.registerTraceClass `hdp.build.atoms            (inherited := true)
  Lean.registerTraceClass `hdp.build.aux_var          (inherited := true)
  Lean.registerTraceClass `hdp.build.problem          (inherited := true)
  Lean.registerTraceClass `hdp.build.cofactors        (inherited := true)
  Lean.registerTraceClass `hdp.build.witnesses        (inherited := true)
  Lean.registerTraceClass `hdp.proof                  (inherited := true)
  Lean.registerTraceClass `hdp.proof.witness_expr     (inherited := true)
  Lean.registerTraceClass `hdp.proof.eqs              (inherited := true)



/-- Running state and monad for normalization -/
structure NormState where
  modAtoms : Array (Expr × Expr) := #[]
  gcdAtoms : Array (Expr × Expr) := #[]
  neqHypNames : Array Name := #[]

abbrev NormM := StateRefT NormState MetaM

namespace NormState

/--
  Register a `m % n` expression into `NormState.modAtoms`
-/
def addModAtom (m n : Expr) : NormM Unit := do
  let s ← get
  unless s.modAtoms.any (· == (m, n)) do
    set { s with modAtoms := s.modAtoms.push (m, n) }

/--
  Register a `gcd m n` expression into `NormState.gcdAtoms`
-/
def addGcdAtom (m n : Expr) : NormM Unit := do
  let s ← get
  unless s.gcdAtoms.any (· == (m, n)) do
    set { s with gcdAtoms := s.gcdAtoms.push (m, n) }

/--
  Register the `Name` of a neq hypothesis
-/
def addneqHypName (userName : Name) : NormM Unit := do
  modify fun s =>
    { s with neqHypNames := s.neqHypNames.push userName}

end NormState



/-- Running state and monad for polynomial translation -/
structure HdpState where
  atoms    : Array Expr := #[]
  polys    : Array P[Rat] := #[]
  -- polySrcs : Array Expr := #[]

abbrev HdpM := StateRefT HdpState MetaM

namespace HdpState

/--
  Lookup or Insert

  Register an atom expression into `HdpState.atoms`, returning its index.
  If the atom is already registered, returns its existing index.
-/
def addAtom (e : Expr) : HdpM Nat := do
  let s ← get
  match s.atoms.findIdx? (· == e) with
  | some i => pure i
  | none   =>
    let i := s.atoms.size
    set { s with atoms := s.atoms.push e }
    pure i

/-- Add a polynomial into `HdpState.polys` -/
def addPoly (p : P[Rat]) : HdpM Unit := do
  modify fun s =>
    { s with polys := s.polys.push p}

end HdpState

end HDP
