/-
  Economy.Productivity
  Acemoglu / Hulten ΔTFP bound.

  FRAMEWORK: Hulten's theorem says that to a first order, a cost reduction
  in an intermediate sector raises aggregate TFP by (sectoral share) × (cost saving).
  Acemoglu (NBER w32487) applies this to AI-exposed tasks and derives a ≤ 0.66%
  10-year TFP bound at point-estimate parameter values.

  We prove the STRUCTURAL inequality (ΔTFP ≤ exposure × costSavings × (1−friction))
  and the tightness at friction = 0. The empirical 0.66% number lives in
  `Economy/Bounds.lean` as a NUMERICAL OBSERVATION.
-/
import Economy.Basic
import Mathlib.Tactic

namespace Economy

/-- Parameters for the Hulten bound.
    `exposure`   — aggregate AI-exposed share (0..1)
    `costSavings`— average cost reduction on exposed tasks (0..1)
    `friction`   — implementation / reallocation friction (0..1);
                   friction = 0 is the frictionless upper bound, friction = 1 kills the gain. -/
structure TFPParams where
  exposure : ℝ
  costSavings : ℝ
  friction : ℝ
  exposure_nonneg : 0 ≤ exposure
  exposure_le_one : exposure ≤ 1
  cost_nonneg : 0 ≤ costSavings
  cost_le_one : costSavings ≤ 1
  fric_nonneg : 0 ≤ friction
  fric_le_one : friction ≤ 1

/-- Realized ΔTFP under the parameterized Hulten formula. -/
def deltaTFP (p : TFPParams) : ℝ :=
  p.exposure * p.costSavings * (1 - p.friction)

/-- THEOREM (Hulten / Acemoglu upper bound):
    ΔTFP ≤ exposure × costSavings. The friction can only reduce the gain. -/
theorem tfp_bound (p : TFPParams) :
    deltaTFP p ≤ p.exposure * p.costSavings := by
  unfold deltaTFP
  have hx : 0 ≤ p.exposure := p.exposure_nonneg
  have hc : 0 ≤ p.costSavings := p.cost_nonneg
  have hf : 0 ≤ p.friction := p.fric_nonneg
  have hxc : 0 ≤ p.exposure * p.costSavings := mul_nonneg hx hc
  nlinarith

/-- THEOREM: the bound is tight at zero friction. -/
theorem tfp_bound_tight (p : TFPParams) (hf : p.friction = 0) :
    deltaTFP p = p.exposure * p.costSavings := by
  unfold deltaTFP
  rw [hf]; ring

/-- THEOREM: ΔTFP is nonnegative. -/
theorem deltaTFP_nonneg (p : TFPParams) : 0 ≤ deltaTFP p := by
  unfold deltaTFP
  have hx := p.exposure_nonneg
  have hc := p.cost_nonneg
  have hf := p.fric_le_one
  have h1f : 0 ≤ 1 - p.friction := by linarith
  positivity

/-- THEOREM: ΔTFP is monotone in exposure (with other parameters fixed). -/
theorem deltaTFP_mono_exposure {p q : TFPParams}
    (h_same_cost : p.costSavings = q.costSavings)
    (h_same_fric : p.friction = q.friction)
    (h_exp : p.exposure ≤ q.exposure) :
    deltaTFP p ≤ deltaTFP q := by
  unfold deltaTFP
  rw [h_same_cost, h_same_fric]
  have hc : 0 ≤ q.costSavings := q.cost_nonneg
  have h1f : 0 ≤ 1 - q.friction := by linarith [q.fric_le_one]
  have hcf : 0 ≤ q.costSavings * (1 - q.friction) := mul_nonneg hc h1f
  nlinarith

/-- THEOREM: ΔTFP is monotone-decreasing in friction. -/
theorem deltaTFP_antitone_friction {p q : TFPParams}
    (h_same_exp : p.exposure = q.exposure)
    (h_same_cost : p.costSavings = q.costSavings)
    (h_fric : p.friction ≤ q.friction) :
    deltaTFP q ≤ deltaTFP p := by
  unfold deltaTFP
  rw [h_same_exp, h_same_cost]
  have hxc : 0 ≤ q.exposure * q.costSavings :=
    mul_nonneg q.exposure_nonneg q.cost_nonneg
  nlinarith

end Economy
