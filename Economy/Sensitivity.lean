/-
  Economy.Sensitivity
  Partial-monotonicity lemmas — how the structural bound reacts to each
  parameter individually. Useful for scenario analysis and for anchoring
  empirical claims in the literature.
-/
import Economy.Productivity
import Economy.GDP
import Mathlib.Tactic

namespace Economy

/-- THEOREM: the TFP gain is bounded above by 1 (100%). Hard ceiling. -/
theorem deltaTFP_le_one (p : TFPParams) : deltaTFP p ≤ 1 := by
  have hbound : deltaTFP p ≤ p.exposure * p.costSavings := tfp_bound p
  have hxc : p.exposure * p.costSavings ≤ 1 := by
    have hx1 := p.exposure_le_one
    have hc1 := p.cost_le_one
    have hx0 := p.exposure_nonneg
    have hc0 := p.cost_nonneg
    nlinarith
  linarith

end Economy
