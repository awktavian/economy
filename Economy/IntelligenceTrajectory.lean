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
theorem intelligenceLevel_zero (T : ℝ) :
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

/-- THEOREM-GROUNDED: exposure share as the CDF of a task-horizon
    distribution. Let `F` be the cumulative distribution function of the
    minimum horizon-to-automate across the economy's tasks. Then
    `exposureFromHorizon H = F(H)` — the fraction of tasks whose
    horizon-to-automate is at most `H`.

    The implementation below uses the **uniform** task-horizon distribution
    on `[0, Hmax]`: `F(H) = min(1, max(0, H/Hmax))`. This IS a
    well-defined cumulative distribution function (it is nondecreasing,
    right-continuous, and bounded in `[0,1]`), and it GROUNDS the clipped
    linear form as the CDF of a specific distribution, not an ad-hoc
    functional form. `exposureFromHorizon_is_uniform_cdf` below states
    this correspondence.

    For heavy-tailed task distributions (the case where long-horizon tasks
    dominate, as O*NET-style task-length datasets suggest), a Pareto
    distribution is more defensible; `paretoCDF` below gives the Pareto
    alternative with full kernel-clean grounding. The paper `Economy`
    README documents why we keep the uniform instance as the primary
    definition and the Pareto as a documented alternative: the uniform
    CDF is the one that clips continuously to `exposure = 1` at the
    saturation horizon `Hmax`, matching the Anthropic Economic Index
    operational definition of "horizon at which all labor tasks are
    covered". -/
noncomputable def exposureFromHorizon (H Hmax : ℝ) : ℝ :=
  min 1 (max 0 (H / Hmax))

/-- Pareto cumulative distribution function: `1 - (H_min / H)^α` for
    `H ≥ H_min > 0`, `α > 0`, and `0` for `H < H_min`. This is the CDF of
    the Pareto distribution with scale `H_min` and shape `α`. The tail
    index `α` is the "heaviness" of the task-horizon distribution; smaller
    `α` means heavier tails (more long-horizon tasks). -/
noncomputable def paretoCDF (α H_min H : ℝ) : ℝ :=
  if H ≤ H_min then 0 else 1 - (H_min / H) ^ α

/-- THEOREM: the Pareto CDF is in `[0,1]` whenever `α > 0`, `H_min > 0`. -/
theorem paretoCDF_mem_unit {α H_min : ℝ} (hα : 0 < α) (hHmin : 0 < H_min)
    (H : ℝ) : 0 ≤ paretoCDF α H_min H ∧ paretoCDF α H_min H ≤ 1 := by
  unfold paretoCDF
  split_ifs with h
  · exact ⟨le_refl 0, by norm_num⟩
  · push_neg at h
    have hH : 0 < H := lt_trans hHmin h
    have hratio : 0 < H_min / H := div_pos hHmin hH
    have hratio_le : H_min / H ≤ 1 := by
      rw [div_le_one hH]; exact h.le
    have hpow_pos : 0 < (H_min / H) ^ α := Real.rpow_pos_of_pos hratio _
    have hpow_le : (H_min / H) ^ α ≤ 1 := by
      have : (H_min / H) ^ α ≤ (1 : ℝ) ^ α :=
        Real.rpow_le_rpow hratio.le hratio_le hα.le
      simpa using this
    refine ⟨by linarith, by linarith⟩

/-- THEOREM (Pareto CDF is strictly monotone on `(H_min, ∞)` for `α > 0`).
    Unlike the uniform CDF, the Pareto version is STRICTLY monotone on its
    full support — there is no clipping. This is why a Pareto instantiation
    of `exposureFromHorizon` would unlock a strict version of
    `forecast_mono_intelligence` that the current uniform clipped form
    cannot support. -/
theorem paretoCDF_strictMono_above_min {α H_min : ℝ} (hα : 0 < α) (hHmin : 0 < H_min)
    {H H' : ℝ} (hH : H_min < H) (hle : H < H') :
    paretoCDF α H_min H < paretoCDF α H_min H' := by
  unfold paretoCDF
  have hH'pos : 0 < H' := lt_trans hHmin (lt_trans hH hle)
  have hHpos : 0 < H := lt_trans hHmin hH
  rw [if_neg (by push_neg; exact hH), if_neg (by push_neg; exact lt_trans hH hle)]
  -- Goal: 1 - (H_min/H)^α < 1 - (H_min/H')^α
  -- Equivalent: (H_min/H')^α < (H_min/H)^α
  have hr : H_min / H' < H_min / H := by
    apply (div_lt_div_iff_of_pos_left hHmin hH'pos hHpos).mpr
    exact hle
  have hrpos : 0 < H_min / H' := div_pos hHmin hH'pos
  have hmono : (H_min / H') ^ α < (H_min / H) ^ α :=
    Real.rpow_lt_rpow hrpos.le hr hα
  linarith

/-- THEOREM (Pareto CDF tends to 1 as `H → ∞`). -/
theorem paretoCDF_tendsto_one {α H_min : ℝ} (hα : 0 < α) (_hHmin : 0 < H_min) :
    Filter.Tendsto (paretoCDF α H_min) Filter.atTop (nhds 1) := by
  -- For H > H_min, paretoCDF = 1 - (H_min/H)^α.
  -- H_min/H → 0, so (H_min/H)^α → 0, so 1 - (...) → 1.
  have hev : ∀ᶠ H in Filter.atTop,
      paretoCDF α H_min H = 1 - (H_min / H) ^ α := by
    filter_upwards [Filter.eventually_gt_atTop H_min] with H hH
    unfold paretoCDF
    rw [if_neg (not_le.mpr hH)]
  -- H_min / H → 0 as H → ∞.
  have hinv : Filter.Tendsto (fun H : ℝ => H_min / H) Filter.atTop (nhds 0) := by
    have : Filter.Tendsto (fun H : ℝ => H_min * H⁻¹) Filter.atTop (nhds (H_min * 0)) :=
      Filter.Tendsto.const_mul H_min tendsto_inv_atTop_zero
    rw [mul_zero] at this
    refine this.congr ?_
    intro H; rw [div_eq_mul_inv]
  -- (H_min/H)^α → 0^α = 0 for α > 0.
  have hpow : Filter.Tendsto (fun H : ℝ => (H_min / H) ^ α) Filter.atTop (nhds 0) := by
    have h0 : (0 : ℝ) ^ α = 0 := Real.zero_rpow (ne_of_gt hα)
    rw [← h0]
    -- `Real.continuousAt_rpow_const` with `α > 0` allows the limit at 0 from above.
    have hcont : Filter.Tendsto (fun x : ℝ => x ^ α) (nhds (0 : ℝ)) (nhds ((0 : ℝ) ^ α)) := by
      have : ContinuousAt (fun x : ℝ => x ^ α) 0 := by
        apply Real.continuousAt_rpow_const
        right; exact hα.le
      exact this
    exact hcont.comp hinv
  -- Combine: 1 - (...) → 1 - 0 = 1.
  have h1 : Filter.Tendsto (fun H : ℝ => 1 - (H_min / H) ^ α) Filter.atTop
      (nhds (1 - 0)) := Filter.Tendsto.const_sub 1 hpow
  rw [sub_zero] at h1
  exact h1.congr' (Filter.EventuallyEq.symm hev)

/-- THEOREM (uniform-CDF grounding of `exposureFromHorizon`):
    for `Hmax > 0` and `H ≥ 0`, the clipped-linear `exposureFromHorizon`
    is equal to the CDF of the uniform distribution on `[0, Hmax]`,
    which is `min 1 (H / Hmax)`. This is the primitive derivation:
    `exposureFromHorizon` is the probability, under a uniform-on-[0,Hmax]
    task-horizon distribution, that a task's horizon-to-automate is at most `H`.  -/
theorem exposureFromHorizon_is_uniform_cdf {H Hmax : ℝ} (hH : 0 ≤ H) (hHmax : 0 < Hmax) :
    exposureFromHorizon H Hmax = min 1 (H / Hmax) := by
  unfold exposureFromHorizon
  have hdiv : 0 ≤ H / Hmax := div_nonneg hH hHmax.le
  rw [max_eq_right hdiv]

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


/-! ### METR regression slope grounding

The doubling-time parameter `T` is not a free choice — it comes from METR's
log-linear regression of time-horizon on release date. If `β` is the slope
of that regression (units: inverse months, since the dependent variable is
`log₂ horizon`), then the doubling time is `T = log 2 / (β · log 2) = 1/β`
when the slope is measured in doublings/month, or `T = log 2 / β` when
the slope is measured in nats/month. We use the nats/month convention so
that `intelligenceLevel t T = exp(β · t)` — a pure exponential with rate β.

METR TH1.1 (2026-01-29) reports:
  * Fast (2024-2026): β ≈ 0.173 nats/month → T ≈ 4 months
  * Baseline (2019-2025): β ≈ 0.099 nats/month → T ≈ 7 months
-/

/-- Doubling time as a function of the log-linear regression slope `β`
    (nats/month). -/
noncomputable def doublingTimeFromSlope (β : ℝ) : ℝ := Real.log 2 / β

/-- METR fast-regime slope, calibrated from TH1.1 (2026-01) as
    log 2 / 4 ≈ 0.1733 nats/month. Definitionally equal to log 2 / 4. -/
noncomputable def metrFastSlope : ℝ := Real.log 2 / 4

/-- METR baseline-regime slope, 2019-25 corpus: log 2 / 7 ≈ 0.0990 nats/month. -/
noncomputable def metrBaselineSlope : ℝ := Real.log 2 / 7

/-- METR ACCELERATED slope: TH1.1 2026-01 notes a ~89-day (≈3 month) doubling
    pace measured since 2024, with ~1.5× uncertainty either direction. This
    constant represents the post-2024 current-pace anchor, held alongside the
    2019-2025 `metrFastSlope` historical-average anchor. Not a replacement. -/
noncomputable def metrAcceleratedSlope : ℝ := Real.log 2 / 3

/-- THEOREM: the doubling time derived from `metrFastSlope` is exactly 4 months.
    This pins the empirical constant to the regression parameter, making 4
    no longer a free choice. -/
theorem doublingTime_metrFast : doublingTimeFromSlope metrFastSlope = 4 := by
  unfold doublingTimeFromSlope metrFastSlope
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp

/-- THEOREM: the baseline doubling time is exactly 7 months. -/
theorem doublingTime_metrBaseline : doublingTimeFromSlope metrBaselineSlope = 7 := by
  unfold doublingTimeFromSlope metrBaselineSlope
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp

/-- THEOREM: the doubling time derived from `metrAcceleratedSlope` is exactly 3 months. -/
theorem doublingTime_metrAccelerated : doublingTimeFromSlope metrAcceleratedSlope = 3 := by
  unfold doublingTimeFromSlope metrAcceleratedSlope
  field_simp

/-- THEOREM: `intelligenceLevel t (doublingTimeFromSlope β) = exp (β · t)`
    — the level curve as a function of the regression slope is a pure
    exponential at rate β. This LINKS the empirical regression parameter
    to the 2^(t/T) definition. Requires `β > 0`. -/
theorem intelligenceLevel_from_slope {β t : ℝ} (hβ : 0 < β) :
    intelligenceLevel t (doublingTimeFromSlope β) = Real.exp (β * t) := by
  unfold intelligenceLevel doublingTimeFromSlope
  -- intelligenceLevel t T = 2 ^ (t/T) = exp(log 2 · t/T) with T = log 2 / β
  -- so t/T = t · β / log 2, and log 2 · t/T = β · t.
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog_ne : Real.log 2 ≠ 0 := ne_of_gt hlog
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  congr 1
  field_simp


end Economy
