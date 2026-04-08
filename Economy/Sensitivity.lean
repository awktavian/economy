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

/-- THEOREM: zero exposure kills the TFP gain entirely. -/
theorem deltaTFP_zero_of_zero_exposure (p : TFPParams) (h : p.exposure = 0) :
    deltaTFP p = 0 := by
  unfold deltaTFP; rw [h]; ring

/-- THEOREM: zero cost savings kills the TFP gain entirely. -/
theorem deltaTFP_zero_of_zero_savings (p : TFPParams) (h : p.costSavings = 0) :
    deltaTFP p = 0 := by
  unfold deltaTFP; rw [h]; ring

/-- THEOREM: full friction kills the TFP gain entirely. -/
theorem deltaTFP_zero_of_full_friction (p : TFPParams) (h : p.friction = 1) :
    deltaTFP p = 0 := by
  unfold deltaTFP; rw [h]; ring

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
