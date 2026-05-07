import HDP.Tactic.Core

namespace HDP

open Lean Elab Tactic Meta

syntax "hdp" : tactic

elab_rules : tactic
  | `(tactic | hdp) => hdpTactic

end HDP
