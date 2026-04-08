/-
  Economy.GDP
  Aggregate GDP change as a function of TFP change and employment change.

  FRAMEWORK: the first-order decomposition d log Y = d log TFP + (labor share) · d log L.
  We write it in level form as an affine function and prove the two monotonicity
  properties that any empirical calibration must respect.
-/
import Economy.Productivity
import Economy.LaborMarket
import Mathlib.Tactic

namespace Economy

/-- GDP-change parameters.
    `laborShare` — labor's share of income (0..1); Acemoglu uses ≈ 0.6 for advanced economies. -/
structure GDPParams where
  tfp : TFPParams
  labor : LaborParams
  laborShare : ℝ
  ls_nonneg : 0 ≤ laborShare
  ls_le_one : laborShare ≤ 1

/-- GDP change (log-linear first order). -/
def gdpDelta (g : GDPParams) : ℝ :=
  deltaTFP g.tfp + g.laborShare * employmentDelta g.labor

/-- THEOREM: GDP delta is monotone in exposure (all else equal). -/
theorem gdpDelta_mono_exposure {g h : GDPParams}
    (h_same_cost : g.tfp.costSavings = h.tfp.costSavings)
    (h_same_fric : g.tfp.friction = h.tfp.friction)
    (h_exp : g.tfp.exposure ≤ h.tfp.exposure)
    (h_same_labor : g.labor = h.labor)
    (h_same_ls : g.laborShare = h.laborShare) :
    gdpDelta g ≤ gdpDelta h := by
  unfold gdpDelta
  have hT : deltaTFP g.tfp ≤ deltaTFP h.tfp :=
    deltaTFP_mono_exposure h_same_cost h_same_fric h_exp
  rw [h_same_labor, h_same_ls]
  linarith

/-- THEOREM: GDP delta is monotone in reinstatement (all else equal). -/
theorem gdpDelta_mono_reinstatement {g h : GDPParams}
    (h_same_tfp : g.tfp = h.tfp)
    (h_disp : g.labor.displacement = h.labor.displacement)
    (h_rein : g.labor.reinstatement ≤ h.labor.reinstatement)
    (h_same_ls : g.laborShare = h.laborShare) :
    gdpDelta g ≤ gdpDelta h := by
  unfold gdpDelta
  have hE : employmentDelta g.labor ≤ employmentDelta h.labor :=
    employmentDelta_mono_rein h_disp h_rein
  have hls : 0 ≤ h.laborShare := h.ls_nonneg
  rw [h_same_tfp, h_same_ls]
  nlinarith

/-- THEOREM: explicit upper envelope:
    gdpDelta ≤ exposure·costSavings + laborShare·reinstatement. -/
theorem gdpDelta_upper_envelope (g : GDPParams) :
    gdpDelta g ≤ g.tfp.exposure * g.tfp.costSavings
                 + g.laborShare * g.labor.reinstatement := by
  unfold gdpDelta employmentDelta
  have hT : deltaTFP g.tfp ≤ g.tfp.exposure * g.tfp.costSavings := tfp_bound g.tfp
  have hls : 0 ≤ g.laborShare := g.ls_nonneg
  have hdisp : 0 ≤ g.labor.displacement := g.labor.disp_nonneg
  have : g.laborShare * (g.labor.reinstatement - g.labor.displacement)
       ≤ g.laborShare * g.labor.reinstatement := by nlinarith
  linarith [hT, this]

end Economy
