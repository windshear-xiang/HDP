import Lean.Elab.Tactic

import HDP.Tactic.Normalize
import HDP.Tactic.ToExpr
import HDP.Data.Buchberger

open Lean Meta Elab Tactic
open Lean.Grind (Field)

namespace HDP

def hdpTactic : TacticM Unit := do
  pure ()

end HDP
