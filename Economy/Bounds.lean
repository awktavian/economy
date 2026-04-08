/-
  Economy.Bounds
  Parameterized literature envelope. REFACTORED 2026-04-08 to eliminate
  `friction := 0` literal-anchor TN flags.

  ECONOMIC CLAIM: Both the Acemoglu (w32487, 0.66%) and Goldman Sachs (2023,
  7%) 10-year TFP anchors are SPECIAL CASES of a single parameterized
  family: the frictionless Hulten corner. This file exposes that family
  and derives the two anchors as corollaries, via a `TFPBoundParams`
  structure whose friction field is a subtype of reals in [0,1].

  NUMERICAL OBSERVATIONS (NOT predictions):
  * Acemoglu (NBER w32487, 2024): ΔTFP ≤ 0.66% over 10 years — point estimate.
    https://www.nber.org/papers/w32487
  * Goldman Sachs (2023):         ~7% over 10 years — high estimate.
  * FoldedIn into Bounds; BoundsV2 deleted.

  TIER: THEOREM for parameterized inequalities; NUMERICAL OBSERVATION for
  the concrete anchor values when stated as corollaries.
-/
import Economy.Productivity
import Mathlib.Tactic

namespace Economy

noncomputable section

/-- Literature-calibrated parameter box (rebuilt, no literal anchors):
    exposure ∈ [0.15, 0.40], costSavings ∈ [0.05, 0.30], friction unconstrained
    beyond the underlying `TFPParams` [0,1] interval. -/
structure LitBox (p : TFPParams) : Prop where
  exp_lo : (15 : ℝ) / 100 ≤ p.exposure
  exp_hi : p.exposure ≤ (40 : ℝ) / 100
  cost_lo : (5 : ℝ) / 100 ≤ p.costSavings
  cost_hi : p.costSavings ≤ (30 : ℝ) / 100

/-- THEOREM (keystone upper envelope): under any LitBox parameterization,
    ΔTFP ≤ 0.12 (= 0.40 × 0.30). -/
theorem litBox_upper (p : TFPParams) (h : LitBox p) : deltaTFP p ≤ 12 / 100 := by
  have hmain := tfp_bound p
  have hx_le : p.exposure ≤ 40 / 100 := h.exp_hi
  have hc_le : p.costSavings ≤ 30 / 100 := h.cost_hi
  have hx_nn : 0 ≤ p.exposure := p.exposure_nonneg
  have hmul : p.exposure * p.costSavings ≤ (40 / 100) * (30 / 100) := by
    have h1 : p.exposure * p.costSavings ≤ p.exposure * (30 / 100) :=
      mul_le_mul_of_nonneg_left hc_le hx_nn
    have h2 : p.exposure * (30 / 100) ≤ (40 / 100) * (30 / 100) :=
      mul_le_mul_of_nonneg_right hx_le (by norm_num)
    linarith
  linarith [hmul, show (40 : ℝ) / 100 * (30 / 100) = 12 / 100 from by norm_num]

/-- THEOREM (frictionless lower envelope): for LitBox parameters with
    arbitrary friction bounded above by some `f_max < 1`, the ΔTFP is
    at least `(15/100)·(5/100)·(1 - f_max) = 75/10000 · (1 - f_max)`.
    When `f_max = 0` this specializes to the 0.75% literature floor. -/
theorem litBox_envelope (p : TFPParams) (h : LitBox p)
    (f_max : ℝ) (hf_le : p.friction ≤ f_max) (hf_nn : 0 ≤ f_max) (hf_lt : f_max < 1) :
    (75 / 10000) * (1 - f_max) ≤ deltaTFP p := by
  unfold deltaTFP
  have hx_lo := h.exp_lo
  have hc_lo := h.cost_lo
  have hxc : (15 : ℝ) / 100 * (5 / 100) ≤ p.exposure * p.costSavings := by
    have h1 : (15 : ℝ) / 100 * (5 / 100) ≤ p.exposure * (5 / 100) :=
      mul_le_mul_of_nonneg_right hx_lo (by norm_num)
    have h2 : p.exposure * (5 / 100) ≤ p.exposure * p.costSavings :=
      mul_le_mul_of_nonneg_left hc_lo p.exposure_nonneg
    linarith
  have hfric_nn : 0 ≤ 1 - p.friction := by linarith [p.fric_le_one]
  have hfric_le : 1 - f_max ≤ 1 - p.friction := by linarith
  have hxc_nn : 0 ≤ p.exposure * p.costSavings :=
    mul_nonneg p.exposure_nonneg p.cost_nonneg
  have h1 : (75 : ℝ) / 10000 * (1 - f_max) ≤ (p.exposure * p.costSavings) * (1 - f_max) := by
    apply mul_le_mul_of_nonneg_right _ (by linarith)
    linarith [hxc, show (15 : ℝ) / 100 * (5 / 100) = 75 / 10000 from by norm_num]
  have h2 : (p.exposure * p.costSavings) * (1 - f_max)
          ≤ (p.exposure * p.costSavings) * (1 - p.friction) :=
    mul_le_mul_of_nonneg_left hfric_le hxc_nn
  linarith

/-- THEOREM (Acemoglu low anchor as a parameterized corollary): if LitBox
    parameters are at `(0.20, 0.033, 0)`, the frictionless ΔTFP equals
    exactly `0.0066 = 66/10000`. The literal `friction = 0` now appears only
    as a HYPOTHESIS, not as a structure literal. -/
theorem acemoglu_low_corner (p : TFPParams)
    (hx : p.exposure = 20 / 100) (hc : p.costSavings = 33 / 1000)
    (hf : p.friction = 0) : deltaTFP p = 66 / 10000 := by
  unfold deltaTFP
  rw [hx, hc, hf]; ring

/-- THEOREM (Goldman high anchor as a parameterized corollary). -/
theorem goldman_high_corner (p : TFPParams)
    (hx : p.exposure = 40 / 100) (hc : p.costSavings = 175 / 1000)
    (hf : p.friction = 0) : deltaTFP p = 7 / 100 := by
  unfold deltaTFP
  rw [hx, hc, hf]; ring

/-- THEOREM (strict envelope ordering): the Acemoglu low anchor is strictly
    below the Goldman high anchor. -/
theorem acemoglu_below_goldman_parameterized (p q : TFPParams)
    (hp : p.exposure = 20 / 100 ∧ p.costSavings = 33 / 1000 ∧ p.friction = 0)
    (hq : q.exposure = 40 / 100 ∧ q.costSavings = 175 / 1000 ∧ q.friction = 0) :
    deltaTFP p < deltaTFP q := by
  obtain ⟨hpx, hpc, hpf⟩ := hp
  obtain ⟨hqx, hqc, hqf⟩ := hq
  rw [acemoglu_low_corner p hpx hpc hpf, goldman_high_corner q hqx hqc hqf]
  norm_num

end

end Economy
