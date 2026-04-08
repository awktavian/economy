/-
  Economy.IntelligenceTrajectory
  Time-parameterized intelligence level with doubling dynamics.

  ECONOMIC CLAIM: AI capability (measured by METR's time-horizon benchmark)
  doubles every T months. At T = 4 months (METR TH1.1, 2026-01) capability
  is on a ×64 / 2 years trajectory; at T = 7 months (2019-25 baseline)
  it is on a ×11 / 2 years trajectory. Task horizon (the longest task the
  frontier model can complete) scales linearly with intelligence level.

  SOURCES:
  * METR Time-Horizon Benchmark TH1.1 (Jan 2026) —
    https://metr.org/blog/2026-1-29-time-horizon-1-1/
  * Anthropic Claude Mythos system card (2026-04-07): 93.9% SWE-bench Verified.
  * Anthropic Economic Index (2025): exposure rises sigmoidally with horizon.

  TIER: THEOREM for monotonicity / doubling identity; FRAMEWORK for the
  sigmoidal exposure mapping (functional form is assumed).
-/
import Economy.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Economy

open Real

/-- Intelligence level at time `t` (months) with doubling time `T` (months).
    `intelligenceLevel t T = 2^(t/T)`, normalized to `intelligenceLevel 0 T = 1`. -/
noncomputable def intelligenceLevel (t T : ℝ) : ℝ := (2 : ℝ) ^ (t / T)

/-- Task horizon at intelligence level `I`, with base horizon `H₀`. Linear
    scaling captures the METR empirical finding that horizon is log-linear
    in time (i.e., linear in the exponentiated intelligence level). -/
noncomputable def taskHorizon (I H₀ : ℝ) : ℝ := H₀ * I

/-- THEOREM: intelligenceLevel is positive. -/
theorem intelligenceLevel_pos (t T : ℝ) : 0 < intelligenceLevel t T := by
  unfold intelligenceLevel
  exact Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _

/-- THEOREM: intelligenceLevel at t=0 is exactly 1 (normalization). -/
theorem intelligenceLevel_zero (T : ℝ) (hT : T ≠ 0) :
    intelligenceLevel 0 T = 1 := by
  unfold intelligenceLevel
  rw [zero_div]
  exact Real.rpow_zero 2

/-- THEOREM (doubling identity): after one doubling time `T`, intelligence
    doubles. Uses the real identity `2^((t+T)/T) = 2 · 2^(t/T)`. -/
theorem doubling_time_inverse (t T : ℝ) (hT : 0 < T) :
    intelligenceLevel (t + T) T = 2 * intelligenceLevel t T := by
  unfold intelligenceLevel
  have hTne : T ≠ 0 := ne_of_gt hT
  have hsplit : (t + T) / T = t / T + 1 := by
    field_simp
  rw [hsplit]
  rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  rw [Real.rpow_one]
  ring

/-- THEOREM: intelligenceLevel is strictly monotone in `t` for positive `T`. -/
theorem intelligenceLevel_strictMono {T : ℝ} (hT : 0 < T) :
    StrictMono (fun t => intelligenceLevel t T) := by
  intro a b hab
  unfold intelligenceLevel
  have h2 : (1 : ℝ) < 2 := by norm_num
  apply Real.rpow_lt_rpow_left_iff h2 |>.mpr
  exact (div_lt_div_iff_of_pos_right hT).mpr hab

/-- THEOREM (k doublings): after `k·T` months, intelligence has grown by `2^k`. -/
theorem intelligenceLevel_k_doublings (k : ℕ) (T : ℝ) (hT : 0 < T) :
    intelligenceLevel (k * T) T = (2 : ℝ) ^ (k : ℝ) := by
  unfold intelligenceLevel
  have hTne : T ≠ 0 := ne_of_gt hT
  have : (↑k * T) / T = (k : ℝ) := by field_simp
  rw [this]

/-- THEOREM: 24 months of T=4mo doubling gives 2^6 = 64× horizon. -/
theorem horizon_bound_years_metr :
    intelligenceLevel 24 4 = 64 := by
  unfold intelligenceLevel
  have h1 : (24 : ℝ) / 4 = 6 := by norm_num
  rw [h1]
  rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) from by norm_num]
  rw [Real.rpow_natCast]
  norm_num

/-- THEOREM: 24 months of T=7mo baseline gives approximately 2^(24/7) ≈ 10.6. -/
theorem horizon_bound_years_baseline_lt :
    intelligenceLevel 24 7 < 11 := by
  unfold intelligenceLevel
  -- 2^(24/7) < 11  iff  24/7 · log 2 < log 11  (take log of both sides)
  -- Equivalently: (24/7) < log 11 / log 2.  log 11 / log 2 ≈ 3.4594, 24/7 ≈ 3.4286.
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have h2log_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- Use monotonicity: x ↦ 2^x is strictly mono; show 24/7 < log₂ 11 via numeric bound.
  -- Simpler: show 2^(24/7) < 2^(35/10) and 2^(35/10) ≤ 11.
  -- We use a direct approach: 11^7 vs 2^24.  11^7 = 19487171.  2^24 = 16777216.
  -- So 2^24 < 11^7, i.e., 2 < 11^(1/7) · ... Let's instead use: 2^(24/7) < 11 iff 2^24 < 11^7.
  have h24_7 : (24 : ℝ) / 7 * 7 = 24 := by norm_num
  -- (2^(24/7))^7 = 2^24 < 11^7 = (11)^7
  have lhs_pow : ((2 : ℝ) ^ ((24 : ℝ) / 7)) ^ (7 : ℕ) = (16777216 : ℝ) := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ ((24 : ℝ) / 7)) 7]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have : (24 : ℝ) / 7 * ((7 : ℕ) : ℝ) = 24 := by push_cast; ring
    rw [this]
    rw [show (24 : ℝ) = ((24 : ℕ) : ℝ) from by norm_num]
    rw [Real.rpow_natCast]
    norm_num
  have lhs_pos : (0 : ℝ) < (2 : ℝ) ^ ((24 : ℝ) / 7) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hineq7 : ((2 : ℝ) ^ ((24 : ℝ) / 7)) ^ (7 : ℕ) < (11 : ℝ) ^ (7 : ℕ) := by
    rw [lhs_pow]
    norm_num
  -- a^7 < b^7 with a,b ≥ 0 implies a < b (strict monotonicity of x ↦ x^7 on ≥0).
  by_contra hge
  push_neg at hge
  have h11_nn : (0 : ℝ) ≤ 11 := by norm_num
  have hmono : (11 : ℝ) ^ (7 : ℕ) ≤ ((2 : ℝ) ^ ((24 : ℝ) / 7)) ^ (7 : ℕ) :=
    pow_le_pow_left₀ h11_nn hge 7
  linarith

/-- FRAMEWORK: exposure share as a monotone bounded function of task horizon.
    We use a clipped-linear model: exposure = min(1, H/Hmax) where Hmax is the
    "horizon at which all labor tasks are covered" (calibrated to 1 year in the
    Anthropic Economic Index). This is the simplest functional form satisfying
    the monotone + bounded constraints. -/
noncomputable def exposureFromHorizon (H Hmax : ℝ) : ℝ :=
  min 1 (max 0 (H / Hmax))

/-- THEOREM: exposureFromHorizon is in [0,1]. -/
theorem exposureFromHorizon_mem_unit (H Hmax : ℝ) :
    0 ≤ exposureFromHorizon H Hmax ∧ exposureFromHorizon H Hmax ≤ 1 := by
  unfold exposureFromHorizon
  refine ⟨?_, ?_⟩
  · exact le_min (by norm_num) (le_max_left _ _)
  · exact min_le_left _ _

/-- THEOREM: exposureFromHorizon is monotone in H (for Hmax > 0). -/
theorem exposureFromHorizon_mono {Hmax : ℝ} (hHmax : 0 < Hmax) {H H' : ℝ}
    (h : H ≤ H') : exposureFromHorizon H Hmax ≤ exposureFromHorizon H' Hmax := by
  unfold exposureFromHorizon
  have hdiv : H / Hmax ≤ H' / Hmax := by
    exact div_le_div_of_nonneg_right h hHmax.le
  have hmax : max 0 (H / Hmax) ≤ max 0 (H' / Hmax) :=
    max_le_max (le_refl 0) hdiv
  exact min_le_min (le_refl 1) hmax

/-- THEOREM: exposure increases weakly with time (composition of monotone maps).
    Captures the forward-propagation of intelligence → horizon → exposure.  -/
theorem exposure_mono_time {T Hmax H₀ : ℝ} (hT : 0 < T) (hHmax : 0 < Hmax)
    (hH₀ : 0 < H₀) {t t' : ℝ} (htt' : t ≤ t') :
    exposureFromHorizon (taskHorizon (intelligenceLevel t T) H₀) Hmax
      ≤ exposureFromHorizon (taskHorizon (intelligenceLevel t' T) H₀) Hmax := by
  apply exposureFromHorizon_mono hHmax
  unfold taskHorizon
  have hI : intelligenceLevel t T ≤ intelligenceLevel t' T := by
    rcases eq_or_lt_of_le htt' with heq | hlt
    · rw [heq]
    · exact le_of_lt (intelligenceLevel_strictMono hT hlt)
  exact mul_le_mul_of_nonneg_left hI hH₀.le

end Economy
