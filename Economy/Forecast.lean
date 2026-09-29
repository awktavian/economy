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
import Mathlib.Analysis.Complex.ExponentialBounds

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
    (hT : 0 < T) (hTle : T ≤ T')
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
    apply gA_antitone_doublingTime s1.T_pos hT s2.H₀_pos s2.Hmax_pos s2.cost_nn ht
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

/-- Zero reinstatement: the `r = 0` endpoint named by the carrier docstring. -/
def zeroReinstatement : Reinstatement where
  r := 0
  r_nn := le_refl 0
  r_le_one := by norm_num

/-- Labor-share retention under reinstatement `r`: `ρ(r) = (1 + r) / 2`, so
    `ρ(0) = 1/2` (zero reinstatement halves the worker's consumption share)
    and `ρ(1) = 1` (full reinstatement: welfare tracks GDP).

    FRAMEWORK: the affine form is a declared functional-form bridge, like the
    exposure → TFP channel above; every theorem below is THEOREM-grade about
    this carrier. -/
noncomputable def retention (R : Reinstatement) : ℝ := (1 + R.r) / 2

/-- THEOREM: `ρ(r) > 0`. Consumes the carrier field `r_nn : 0 ≤ r`. -/
theorem retention_pos (R : Reinstatement) : 0 < retention R := by
  unfold retention
  linarith [R.r_nn]

/-- THEOREM: `ρ(r) ≤ 1`. Consumes the carrier field `r_le_one : r ≤ 1`. -/
theorem retention_le_one (R : Reinstatement) : retention R ≤ 1 := by
  unfold retention
  linarith [R.r_le_one]

/-- `gA` is bounded by `costSavings`: exposure lies in `[0, 1]`. -/
theorem gA_le_costSavings (s : Scenario) (t : ℝ) : s.gA t ≤ s.costSavings := by
  unfold gA
  have hmem := exposureFromHorizon_mem_unit
    (taskHorizon (intelligenceLevel t s.T) s.H₀) s.Hmax
  have := mul_le_mul_of_nonneg_right hmem.2 s.cost_nn
  rw [one_mul] at this
  exact this

/-- The representative worker's consumption at time `t`: baseline `C₀`, grown
    along the scenario's log-GDP deviation, scaled by labor-share retention. -/
noncomputable def reinstatedConsumption (C₀ : ℝ) (s : Scenario)
    (R : Reinstatement) (t : ℝ) : ℝ :=
  C₀ * retention R * Real.exp (s.logGDPDeviation t)

/-- THEOREM (welfare through the `Reinstatement` carrier): the welfare change
    decomposes as `log ρ(r) + logGDPDeviation t`. The carrier's `r_nn` field
    is consumed: positivity of `ρ` makes the logarithm total at each factor. -/
theorem welfareDelta_reinstated (C₀ : ℝ) (hC₀ : 0 < C₀) (s : Scenario)
    (R : Reinstatement) (t : ℝ) :
    welfareDelta C₀ (reinstatedConsumption C₀ s R t) =
      Real.log (retention R) + s.logGDPDeviation t := by
  unfold welfareDelta
  have hρ : 0 < retention R := retention_pos R
  have h1 : Real.log ((C₀ * retention R) * Real.exp (s.logGDPDeviation t))
      = Real.log (C₀ * retention R) + s.logGDPDeviation t := by
    rw [Real.log_mul (ne_of_gt (mul_pos hC₀ hρ)) (ne_of_gt (Real.exp_pos _)),
        Real.log_exp]
  have hX : reinstatedConsumption C₀ s R t
      = (C₀ * retention R) * Real.exp (s.logGDPDeviation t) := rfl
  rw [hX, h1, Real.log_mul (ne_of_gt hC₀) (ne_of_gt hρ)]
  ring

/-- THEOREM (divergence criterion through the carrier): if GDP rises
    (`0 < logGDPDeviation t`) but by strictly less than `log 2`, then zero
    reinstatement (`r = 0`) makes welfare strictly fall. -/
theorem welfare_falls_at_zero_reinstatement (C₀ : ℝ) (hC₀ : 0 < C₀) (s : Scenario)
    (R : Reinstatement) (hR0 : R.r = 0) {t : ℝ}
    (_hpos : 0 < s.logGDPDeviation t) (hlt : s.logGDPDeviation t < Real.log 2) :
    welfareDelta C₀ (reinstatedConsumption C₀ s R t) < 0 := by
  have hρ : retention R = 1 / 2 := by
    unfold retention
    rw [hR0]
    norm_num
  rw [welfareDelta_reinstated C₀ hC₀ s R t, hρ,
      Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0),
      Real.log_one]
  linarith

/-- THEOREM (the carrier bounds welfare by the GDP deviation): for every
    reinstatement parameter and every time, the welfare change is at most the
    log-GDP deviation. Consumes `r_le_one` through `retention_le_one`. -/
theorem welfare_le_logGDPDeviation (C₀ : ℝ) (hC₀ : 0 < C₀) (s : Scenario)
    (R : Reinstatement) (t : ℝ) :
    welfareDelta C₀ (reinstatedConsumption C₀ s R t) ≤ s.logGDPDeviation t := by
  rw [welfareDelta_reinstated C₀ hC₀ s R t]
  have : Real.log (retention R) ≤ retention R - 1 :=
    Real.log_le_sub_one_of_pos (retention_pos R)
  linarith [retention_le_one R]

/-- THEOREM (full reinstatement: welfare tracks GDP): with `r = 1` the
    welfare change equals the log-GDP deviation, so a nonnegatively rising
    forecast raises welfare — the docstring's `r = 1` regime, now proved. -/
theorem welfare_tracks_gdp_at_full_reinstatement (C₀ : ℝ) (hC₀ : 0 < C₀)
    (s : Scenario) (R : Reinstatement) (hR1 : R.r = 1) {t : ℝ}
    (ht : 0 ≤ s.logGDPDeviation t) :
    0 ≤ welfareDelta C₀ (reinstatedConsumption C₀ s R t) := by
  have hρ : retention R = 1 := by
    unfold retention
    rw [hR1]
    norm_num
  rw [welfareDelta_reinstated C₀ hC₀ s R t, hρ, Real.log_one]
  linarith

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

/-- THEOREM (welfare–GDP divergence, through the `Reinstatement` carrier):
    there exist a scenario, a reinstatement parameter with `r = 0`, a
    baseline `C₀ > 0`, and a time `t > 0` at which the log-GDP deviation is
    strictly positive while the representative worker's welfare change is
    strictly negative.

    This replaces the former `welfare_trajectory_can_diverge_from_gdp`,
    whose statement was `∃ Y Y' lam lam', …` — it quantified over none of
    the objects its docstring named (no scenario, no reinstatement
    parameter, no time, no `logGDPDeviation`), routing around `Reinstatement`
    entirely. The carrier is now load-bearing: `r_nn` and `r_le_one` are
    consumed as literal hypotheses in `Scenario.welfareDelta_reinstated` and
    `Scenario.welfare_le_logGDPDeviation`, and the witnessing scenario
    `metrFastScenario` at `t = 1` has a *provably* positive log-GDP
    deviation bounded by the one-month growth `0.1762 < log 2`, so the
    `r = 0` halving dominates. -/
theorem welfare_GDP_divergence_via_Reinstatement :
    ∃ (s : Scenario) (R : Scenario.Reinstatement) (C₀ t : ℝ),
      R.r = 0 ∧ 0 < C₀ ∧ 0 < t ∧ 0 < s.logGDPDeviation t ∧
        welfareDelta C₀ (Scenario.reinstatedConsumption C₀ s R t) < 0 := by
  refine ⟨metrFastScenario, Scenario.zeroReinstatement, 1, 1,
    rfl, zero_lt_one, zero_lt_one, ?_, ?_⟩
  · have hpos : 0 < metrFastScenario.logGDPDeviation 1 := by
      show 0 < (metrFastScenario.gA 1 + (1 - metrFastScenario.α)
        * metrFastScenario.gK) * 1
      rw [mul_one]
      have hgK : (0 : ℝ) < (1 - metrFastScenario.α) * metrFastScenario.gK := by
        show (1 - (6 : ℝ) / 10) * (3 / 1000) > 0
        norm_num
      linarith [Scenario.gA_nonneg metrFastScenario 1, hgK]
    exact hpos
  · refine Scenario.welfare_falls_at_zero_reinstatement 1 zero_lt_one
      metrFastScenario Scenario.zeroReinstatement rfl ?_ ?_
    · show 0 < (metrFastScenario.gA 1 + (1 - metrFastScenario.α)
        * metrFastScenario.gK) * 1
      rw [mul_one]
      have hgK : (0 : ℝ) < (1 - metrFastScenario.α) * metrFastScenario.gK := by
        show (1 - (6 : ℝ) / 10) * (3 / 1000) > 0
        norm_num
      linarith [Scenario.gA_nonneg metrFastScenario 1, hgK]
    · show (metrFastScenario.gA 1 + (1 - metrFastScenario.α)
        * metrFastScenario.gK) * 1 < Real.log 2
      rw [mul_one]
      have hle := Scenario.gA_le_costSavings metrFastScenario 1
      have hnum : (175 : ℝ) / 1000 + (1 - 6 / 10) * (3 / 1000) = 1762 / 10000 := by
        norm_num
      have hlt : (1762 : ℝ) / 10000 < Real.log 2 :=
        lt_trans (by norm_num : (1762 : ℝ) / 10000 < 0.6931471803)
          Real.log_two_gt_d9
      have hcs : metrFastScenario.costSavings = (175 : ℝ) / 1000 := rfl
      have hgK : (1 - metrFastScenario.α) * metrFastScenario.gK
          = (1 - (6 : ℝ) / 10) * (3 / 1000) := rfl
      linarith [hle, hcs, hgK, hnum, hlt]

end Economy
