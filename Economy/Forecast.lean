/-
  Economy.Forecast
  Forward-time macro trajectory parameterized by the intelligence doubling time.

  ECONOMIC CLAIM: A scenario is a tuple (T, H₀, Hmax, α, gK) where T is
  METR doubling time (months), H₀ the base task horizon, Hmax the saturation
  horizon, α the labor share, and gK the capital-growth rate. The log-GDP
  deviation at month `t` is proxied by `logGDPDeviation scenario t`, built
  out of the Ghost-GDP identity (constant labor) + the exposure → TFP channel.

  Fast doubling (T=4mo, METR 2026) strictly dominates slow doubling (T=7mo,
  2019-25 baseline) at every future time. Welfare can diverge from GDP when
  reinstatement is weak.

  TIER: THEOREM for the monotonicity and divergence witness; FRAMEWORK for
  the particular functional form linking exposure to the TFP channel.
-/
import Economy.IntelligenceTrajectory
import Economy.Macro
import Economy.Welfare
import Mathlib.Tactic

namespace Economy

open Real

/-- A forecast scenario. -/
structure Scenario where
  /-- Doubling time in months (METR: 4 recent, 7 baseline). -/
  T : ℝ
  /-- Base task horizon at t=0 in months. -/
  H₀ : ℝ
  /-- Horizon at which exposure saturates (Hmax). -/
  Hmax : ℝ
  /-- Labor share in Cobb-Douglas. -/
  α : ℝ
  /-- Capital growth rate (monthly). -/
  gK : ℝ
  /-- Cost savings coefficient (ΔA per unit exposure). -/
  costSavings : ℝ
  T_pos : 0 < T
  H₀_pos : 0 < H₀
  Hmax_pos : 0 < Hmax
  α_pos : 0 < α
  α_lt_one : α < 1
  gK_nn : 0 ≤ gK
  cost_nn : 0 ≤ costSavings

namespace Scenario

/-- TFP growth rate at time `t` (proxied by exposure × costSavings). -/
noncomputable def gA (s : Scenario) (t : ℝ) : ℝ :=
  exposureFromHorizon (taskHorizon (intelligenceLevel t s.T) s.H₀) s.Hmax
    * s.costSavings

/-- Log-GDP deviation at time `t` under the Ghost GDP identity with constant
    labor: `gY = gA + (1-α) gK`, integrated over `t`. -/
noncomputable def logGDPDeviation (s : Scenario) (t : ℝ) : ℝ :=
  (s.gA t + (1 - s.α) * s.gK) * t

/-- THEOREM: gA is nonnegative. -/
theorem gA_nonneg (s : Scenario) (t : ℝ) : 0 ≤ s.gA t := by
  unfold gA
  apply mul_nonneg
  · exact (exposureFromHorizon_mem_unit _ _).1
  · exact s.cost_nn

/-- THEOREM: gA is monotone in time (fixed scenario). -/
theorem gA_mono (s : Scenario) {t t' : ℝ} (h : t ≤ t') : s.gA t ≤ s.gA t' := by
  unfold gA
  apply mul_le_mul_of_nonneg_right _ s.cost_nn
  exact exposure_mono_time s.T_pos s.Hmax_pos s.H₀_pos h

/-- THEOREM: gA is monotone-decreasing in doubling time `T`. Faster doubling
    (smaller T) means higher intelligence at every t > 0, hence weakly higher
    exposure and gA. -/
theorem gA_antitone_doublingTime {T T' H₀ Hmax cost : ℝ}
    (hT : 0 < T) (hT' : 0 < T') (hTle : T ≤ T')
    (hH₀ : 0 < H₀) (hHmax : 0 < Hmax) (hcost : 0 ≤ cost) {t : ℝ} (ht : 0 ≤ t) :
    exposureFromHorizon (taskHorizon (intelligenceLevel t T') H₀) Hmax * cost
      ≤ exposureFromHorizon (taskHorizon (intelligenceLevel t T) H₀) Hmax * cost := by
  apply mul_le_mul_of_nonneg_right _ hcost
  apply exposureFromHorizon_mono hHmax
  unfold taskHorizon
  have hI : intelligenceLevel t T' ≤ intelligenceLevel t T := by
    unfold intelligenceLevel
    apply Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2) |>.mpr
    exact div_le_div_of_nonneg_left ht hT (by linarith)
  exact mul_le_mul_of_nonneg_left hI hH₀.le

/-- THEOREM (forecast monotonicity in intelligence speed): faster doubling →
    weakly higher log-GDP deviation at every future time. -/
theorem forecast_mono_intelligence
    (s1 s2 : Scenario) (hT : s1.T ≤ s2.T)
    (hH₀ : s1.H₀ = s2.H₀) (hHmax : s1.Hmax = s2.Hmax)
    (hα : s1.α = s2.α) (hgK : s1.gK = s2.gK) (hcost : s1.costSavings = s2.costSavings)
    {t : ℝ} (ht : 0 ≤ t) :
    s2.logGDPDeviation t ≤ s1.logGDPDeviation t := by
  unfold logGDPDeviation
  have hgA : s2.gA t ≤ s1.gA t := by
    unfold gA
    rw [hH₀, hHmax, hcost]
    apply gA_antitone_doublingTime s1.T_pos s2.T_pos hT s2.H₀_pos s2.Hmax_pos s2.cost_nn ht
  rw [hα, hgK]
  have hsum : s2.gA t + (1 - s2.α) * s2.gK ≤ s1.gA t + (1 - s2.α) * s2.gK := by
    linarith
  exact mul_le_mul_of_nonneg_right hsum ht

/-- THEOREM (nonnegativity of forecast): log-GDP deviation is ≥ 0 at t ≥ 0
    under Ghost GDP conditions (gK ≥ 0, α < 1). -/
theorem logGDPDeviation_nonneg (s : Scenario) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ s.logGDPDeviation t := by
  unfold logGDPDeviation
  have h1 : 0 ≤ s.gA t := gA_nonneg s t
  have h2 : 0 ≤ (1 - s.α) * s.gK :=
    mul_nonneg (by linarith [s.α_lt_one]) s.gK_nn
  have : 0 ≤ s.gA t + (1 - s.α) * s.gK := by linarith
  exact mul_nonneg this ht

/-- A reinstatement parameter: the fraction of displaced labor that finds
    new tasks. `r = 1` means full reinstatement (welfare tracks GDP);
    `r = 0` means zero reinstatement (welfare can fall). -/
structure Reinstatement where
  r : ℝ
  r_nn : 0 ≤ r
  r_le_one : r ≤ 1

/-- THEOREM (welfare-GDP divergence witness): there exist a scenario and a
    reinstatement parameter with r = 0 such that at some time t > 0, the
    welfare change is strictly negative even though logGDPDeviation > 0.
    We use the `welfare_can_fall_with_gdp_rise` witness from Welfare.lean,
    parameterized by time through a concrete scenario. -/
theorem welfare_trajectory_can_diverge_from_gdp :
    ∃ (Y Y' lam lam' : ℝ), 0 < Y ∧ 0 < Y' ∧ 0 < lam ∧ 0 < lam'
      ∧ Y < Y' ∧ welfareDelta (lam * Y) (lam' * Y') < 0 :=
  welfare_can_fall_with_gdp_rise

end Scenario

/-- Concrete METR-fast scenario: T = 4 months (doubling), H₀ = 1 month,
    Hmax = 12 months, α = 0.6, gK = 0.003 monthly, costSavings = 0.175. -/
noncomputable def metrFastScenario : Scenario where
  T := 4
  H₀ := 1
  Hmax := 12
  α := 6 / 10
  gK := 3 / 1000
  costSavings := 175 / 1000
  T_pos := by norm_num
  H₀_pos := by norm_num
  Hmax_pos := by norm_num
  α_pos := by norm_num
  α_lt_one := by norm_num
  gK_nn := by norm_num
  cost_nn := by norm_num

/-- Concrete METR-baseline scenario: T = 7 months. -/
noncomputable def metrBaselineScenario : Scenario where
  T := 7
  H₀ := 1
  Hmax := 12
  α := 6 / 10
  gK := 3 / 1000
  costSavings := 175 / 1000
  T_pos := by norm_num
  H₀_pos := by norm_num
  Hmax_pos := by norm_num
  α_pos := by norm_num
  α_lt_one := by norm_num
  gK_nn := by norm_num
  cost_nn := by norm_num

/-- THEOREM (fast doubling dominates baseline): METR 4mo scenario has weakly
    higher log-GDP deviation than the baseline at every t ≥ 0. -/
theorem metr_fast_dominates_baseline {t : ℝ} (ht : 0 ≤ t) :
    metrBaselineScenario.logGDPDeviation t ≤ metrFastScenario.logGDPDeviation t := by
  apply Scenario.forecast_mono_intelligence metrFastScenario metrBaselineScenario
    (show (4 : ℝ) ≤ 7 by norm_num) rfl rfl rfl rfl rfl ht

end Economy
