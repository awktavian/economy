/-
  Economy.Bounds
  Numerical envelope anchoring the structural theorems in empirical literature.

  NUMERICAL OBSERVATIONS (NOT predictions):
  * Acemoglu (NBER w32487, 2024): ΔTFP ≤ 0.66% over 10 years under point estimates.
  * Goldman Sachs (2023):         ~7% over 10 years under the high estimate.
  These are used only to build a sensitivity envelope around the structural bound
  proved in `Economy/Productivity.lean`.
-/
import Economy.Productivity
import Mathlib.Tactic

namespace Economy

noncomputable section

/-- Anthropic/Acemoglu LOW anchor: exposure 0.2, costSavings 0.033, friction 0.
    Product = 0.0066 = 0.66%. This matches Acemoglu's 10-year point estimate. -/
def acemogluLow : TFPParams where
  exposure := (2 : ℝ) / 10
  costSavings := (33 : ℝ) / 1000
  friction := 0
  exposure_nonneg := by norm_num
  exposure_le_one := by norm_num
  cost_nonneg := by norm_num
  cost_le_one := by norm_num
  fric_nonneg := le_refl 0
  fric_le_one := by norm_num

/-- THEOREM: at the Acemoglu low anchor, ΔTFP equals exactly 0.0066. -/
theorem acemoglu_low_exact : deltaTFP acemogluLow = 66 / 10000 := by
  unfold deltaTFP acemogluLow
  norm_num

/-- THEOREM: ΔTFP at the Acemoglu low anchor is ≤ 0.0066 (trivial corollary;
    restated in the form Acemoglu uses in the abstract of w32487). -/
theorem acemoglu_envelope_low : deltaTFP acemogluLow ≤ 66 / 10000 := by
  rw [acemoglu_low_exact]

/-- Goldman Sachs HIGH anchor: exposure 0.4, costSavings 0.175, friction 0.
    Product = 0.07 = 7%. This matches Goldman's 2023 ~7% 10-year high estimate. -/
def goldmanHigh : TFPParams where
  exposure := (4 : ℝ) / 10
  costSavings := (175 : ℝ) / 1000
  friction := 0
  exposure_nonneg := by norm_num
  exposure_le_one := by norm_num
  cost_nonneg := by norm_num
  cost_le_one := by norm_num
  fric_nonneg := le_refl 0
  fric_le_one := by norm_num

/-- THEOREM: at the Goldman high anchor, ΔTFP equals exactly 0.07. -/
theorem goldman_high_exact : deltaTFP goldmanHigh = 7 / 100 := by
  unfold deltaTFP goldmanHigh
  norm_num

/-- THEOREM: the low anchor's structural bound is strictly below the high anchor's.
    This is the "envelope width" of the literature. -/
theorem acemoglu_below_goldman :
    deltaTFP acemogluLow < deltaTFP goldmanHigh := by
  rw [acemoglu_low_exact, goldman_high_exact]
  norm_num

end

end Economy
