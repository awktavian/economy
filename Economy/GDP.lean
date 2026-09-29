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

/-! ### Carrier consumption — GDPParams from the TFP and Labor witnesses

`gdpDelta_mono_exposure`, `gdpDelta_mono_reinstatement` and
`gdpDelta_upper_envelope` quantify over all of `GDPParams`. The structure is
the bundle `tfp : TFPParams`, `labor : LaborParams`, `laborShare ∈ [0,1]`;
it becomes a one-liner once the Goldman TFP corner (`Economy.tfpGoldmanCorner`)
and the two signed flow witnesses (`Economy.laborDisplaced` /
`Economy.laborReinstated`) exist. The labor share 0.60 is the BEA /
Acemoglu value cited in this file's header; the displacement anchor −6% for
22–25-year-olds in high-AI-exposure occupations is Brynjolfsson–Chandar–Chen
(2025) as recorded in `Economy.Empirical` and `REFERENCES.md` §4. -/

/-- Displacement corner: Goldman TFP corner × displaced flows × labor share
    0.60. First-order GDP change: 0.07 − 0.6·0.06 = 3.4%. -/
noncomputable def gdpDisplacedBEA : GDPParams where
  tfp := tfpGoldmanCorner
  labor := laborDisplaced
  laborShare := 6 / 10
  ls_nonneg := by norm_num
  ls_le_one := by norm_num

/-- Reinstatement corner: the same TFP corner × reinstated flows
    (reinstatement 0.01, displacement 0). First-order GDP change 7.6%. -/
noncomputable def gdpReinstatedBEA : GDPParams where
  tfp := tfpGoldmanCorner
  labor := laborReinstated
  laborShare := 6 / 10
  ls_nonneg := by norm_num
  ls_le_one := by norm_num

/-- THEOREM (anchor pin, displacement corner): the first-order GDP change
    at `gdpDisplacedBEA` is exactly 34/1000 — positive, i.e. at this
    calibration the 7% TFP gain outweighs the 0.6·6% = 3.6% displacement
    drag. Model computation at chosen data, not a measurement. -/
theorem gdpDelta_gdpDisplacedBEA : gdpDelta gdpDisplacedBEA = 34 / 1000 := by
  have h1 : gdpDisplacedBEA.tfp.exposure = (40 : ℝ) / 100 := rfl
  have h2 : gdpDisplacedBEA.tfp.costSavings = (175 : ℝ) / 1000 := rfl
  have h3 : gdpDisplacedBEA.tfp.friction = 0 := rfl
  have h4 : gdpDisplacedBEA.labor.reinstatement = 0 := rfl
  have h5 : gdpDisplacedBEA.labor.displacement = (6 : ℝ) / 100 := rfl
  have h6 : gdpDisplacedBEA.laborShare = (6 : ℝ) / 10 := rfl
  unfold gdpDelta deltaTFP employmentDelta
  rw [h1, h2, h3, h4, h5, h6]
  norm_num

/-- THEOREM (anchor pin, reinstatement corner): 76/1000. -/
theorem gdpDelta_gdpReinstatedBEA : gdpDelta gdpReinstatedBEA = 76 / 1000 := by
  have h1 : gdpReinstatedBEA.tfp.exposure = (40 : ℝ) / 100 := rfl
  have h2 : gdpReinstatedBEA.tfp.costSavings = (175 : ℝ) / 1000 := rfl
  have h3 : gdpReinstatedBEA.tfp.friction = 0 := rfl
  have h4 : gdpReinstatedBEA.labor.reinstatement = (1 : ℝ) / 100 := rfl
  have h5 : gdpReinstatedBEA.labor.displacement = 0 := rfl
  have h6 : gdpReinstatedBEA.laborShare = (6 : ℝ) / 10 := rfl
  unfold gdpDelta deltaTFP employmentDelta
  rw [h1, h2, h3, h4, h5, h6]
  norm_num

/-- THEOREM (envelope binds at the displacement corner): with
    `reinstatement = 0` the `gdpDelta_upper_envelope` ceiling is exactly
    the 7% frictionless TFP corner. -/
theorem gdpDisplacedBEA_le_envelope : gdpDelta gdpDisplacedBEA ≤ 7 / 100 := by
  rw [gdpDelta_gdpDisplacedBEA]
  norm_num

end Economy
