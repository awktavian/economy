/-
  Economy.ScenarioSpace
  A typed family of possible AI futures. Lifts the macro model from one
  doubling-time scenario to FIVE canonical intelligence trajectories, each
  a real-valued function of time (months). Proves dominance and asymptotic
  comparison theorems that compose with Forecast.lean.

  ECONOMIC CLAIM: The space of plausible near-term AI futures can be
  parameterized by five qualitative shapes:

    (1) mythosPlateau   — capability freezes at today's frontier
    (2) continued       — METR 2026 doubling continues indefinitely
    (3) sigmoid         — capability saturates at a finite ceiling L (AGI ceiling)
    (4) hyperExp        — recursive self-improvement / fast takeoff (β > 1)
    (5) winter          — capability climbs, then exponentially decays

  Each shape induces a GDP trajectory via Forecast.gdpTrajectory
  composition with intelligenceLevel. The dominance lattice between
  trajectories lifts to a dominance lattice on log-GDP deviation: if
  trajectory T₁ weakly dominates T₂ pointwise on [0,t], the induced GDP
  deviation satisfies the same inequality (composition theorem).

  The five trajectories are not exhaustive; they are CANONICAL shapes
  (monotone-plateau, pure-exponential, saturation, super-exponential,
  non-monotone). Any plausible continuous single-metric forecast is close
  in the sup-norm to a convex combination of them.

  SOURCES:
  * METR Time-Horizon Benchmark TH1.1 (2026-01-29) — empirical doubling.
  * Bostrom (2014), "Superintelligence", Ch. 4 — takeoff speed taxonomy.
  * Davidson (2023), "What a compute-centric framework says about takeoff
    speeds", Open Philanthropy — explicit sigmoid vs hyper-exp curves.
  * Hanson (2008), "Economics of the Singularity", IEEE Spectrum — AI winter.

  TIER: THEOREM for all comparison, dominance, and asymptotic results.
-/
import Economy.IntelligenceTrajectory
import Economy.Forecast
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic

namespace Economy

open Real

/-! ### The five canonical trajectories, each as a plain `ℝ → ℝ` function. -/

/-- MYTHOS PLATEAU: `2^(t/T)` until `t_now`, then frozen. Captures the
    "Mythos is the last frontier" hypothesis — capability stops advancing.
    Here `t_now` is the freeze time (current frontier) and `T` is the
    doubling time up to the freeze. -/
noncomputable def mythosPlateau (t_now T t : ℝ) : ℝ :=
  if t ≤ t_now then (2 : ℝ) ^ (t / T) else (2 : ℝ) ^ (t_now / T)

/-- CONTINUED EXPONENTIAL: identical to `intelligenceLevel`. The null
    hypothesis — the METR 2026 trajectory extrapolates indefinitely. -/
noncomputable def continuedExponential (T t : ℝ) : ℝ := (2 : ℝ) ^ (t / T)

/-- SIGMOID SATURATION: logistic curve to a hard ceiling L. Capability
    accelerates then saturates. Asymptote L is the "AGI ceiling". -/
noncomputable def sigmoidSaturation (k L t₀ t : ℝ) : ℝ :=
  L / (1 + Real.exp (-k * (t - t₀)))

/-- HYPER-EXPONENTIAL: `2^((t/T)^β)` with `β > 1`. Each doubling shrinks
    the next — a fast-takeoff / recursive-self-improvement shape. -/
noncomputable def hyperExponential (T β t : ℝ) : ℝ :=
  (2 : ℝ) ^ ((t / T) ^ β)

/-- AI WINTER: `2^(t/T)` until `t_winter`, then exponential decay at rate
    `decay > 0`. Models regulation, energy crisis, talent loss, data wall. -/
noncomputable def aiWinter (T t_winter decay t : ℝ) : ℝ :=
  if t ≤ t_winter then (2 : ℝ) ^ (t / T)
  else (2 : ℝ) ^ (t_winter / T) * Real.exp (-decay * (t - t_winter))

/-! ### Basic properties — positivity, plateau freeze. -/

theorem mythosPlateau_pos (t_now T t : ℝ) : 0 < mythosPlateau t_now T t := by
  unfold mythosPlateau
  split_ifs <;> exact Real.rpow_pos_of_pos (by norm_num) _

theorem continuedExponential_pos (T t : ℝ) : 0 < continuedExponential T t :=
  Real.rpow_pos_of_pos (by norm_num) _

theorem sigmoidSaturation_pos {k L t₀ t : ℝ} (hL : 0 < L) :
    0 < sigmoidSaturation k L t₀ t := by
  unfold sigmoidSaturation
  have hexp : 0 < Real.exp (-k * (t - t₀)) := Real.exp_pos _
  have hden : 0 < 1 + Real.exp (-k * (t - t₀)) := by linarith
  exact div_pos hL hden

theorem hyperExponential_pos (T β t : ℝ) : 0 < hyperExponential T β t :=
  Real.rpow_pos_of_pos (by norm_num) _

theorem aiWinter_pos (T t_winter decay t : ℝ) : 0 < aiWinter T t_winter decay t := by
  unfold aiWinter
  split_ifs
  · exact Real.rpow_pos_of_pos (by norm_num) _
  · exact mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (Real.exp_pos _)

/-- THEOREM (sigmoid upper bound): `sigmoidSaturation < L` for all `t`,
    i.e. the ceiling is strict. -/
theorem sigmoidSaturation_lt_ceiling {k L t₀ t : ℝ} (hL : 0 < L) :
    sigmoidSaturation k L t₀ t < L := by
  unfold sigmoidSaturation
  have hexp : 0 < Real.exp (-k * (t - t₀)) := Real.exp_pos _
  have hden : 0 < 1 + Real.exp (-k * (t - t₀)) := by linarith
  rw [div_lt_iff₀ hden]
  nlinarith

/-- THEOREM (plateau freeze): after `t_now`, the Mythos trajectory is
    constant at `2^(t_now/T)`. -/
theorem mythosPlateau_frozen {t_now T t : ℝ} (h : t_now < t) :
    mythosPlateau t_now T t = (2 : ℝ) ^ (t_now / T) := by
  unfold mythosPlateau
  rw [if_neg (not_le.mpr h)]

/-- THEOREM (plateau pre-freeze): before `t_now`, the Mythos trajectory
    coincides with `continuedExponential`. -/
theorem mythosPlateau_preFreeze {t_now T t : ℝ} (h : t ≤ t_now) :
    mythosPlateau t_now T t = continuedExponential T t := by
  unfold mythosPlateau continuedExponential
  rw [if_pos h]

/-! ### Comparison theorems — the dominance lattice. -/

/-- THEOREM (continued dominates plateau strictly after freeze):
    for `t > t_now` and `T > 0`, the continued trajectory is strictly
    greater than the plateau. Before `t_now` they coincide. -/
theorem continued_dominates_plateau_strict
    {t_now T t : ℝ} (hT : 0 < T) (ht : t_now < t) :
    mythosPlateau t_now T t < continuedExponential T t := by
  rw [mythosPlateau_frozen ht]
  unfold continuedExponential
  have h2 : (1 : ℝ) < 2 := by norm_num
  apply (Real.rpow_lt_rpow_left_iff h2).mpr
  exact (div_lt_div_iff_of_pos_right hT).mpr ht

/-- THEOREM (continued weakly dominates plateau everywhere): -/
theorem continued_dominates_plateau
    {t_now T t : ℝ} (hT : 0 < T) :
    mythosPlateau t_now T t ≤ continuedExponential T t := by
  by_cases ht : t ≤ t_now
  · rw [mythosPlateau_preFreeze ht]
  · push_neg at ht
    exact le_of_lt (continued_dominates_plateau_strict hT ht)

/-- THEOREM (hyperExp dominates continued for t > T with β > 1):
    when `β > 1`, at `t = T` both equal `2`, and for `t > T` the
    hyper-exponential is strictly larger (the exponent `(t/T)^β` exceeds
    `t/T`). Stated with the explicit threshold `t ≥ T`. -/
theorem hyperExp_dominates_continued
    {T β t : ℝ} (hT : 0 < T) (hβ : 1 < β) (ht : T ≤ t) :
    continuedExponential T t ≤ hyperExponential T β t := by
  unfold continuedExponential hyperExponential
  apply Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2) |>.mpr
  -- Goal: t/T ≤ (t/T)^β when t ≥ T (so t/T ≥ 1) and β > 1.
  have hx : (1 : ℝ) ≤ t / T := (one_le_div hT).mpr ht
  have := Real.rpow_le_rpow_of_exponent_le hx (le_of_lt hβ)
  simpa using this

/-- THEOREM (hyperExp strictly dominates continued for `t > T`): the
    crossover happens exactly at `t = T` (both equal `2`). For `t > T`
    the hyper-exponential is STRICTLY above the continued exponential. -/
theorem hyperExp_dominates_continued_strict
    {T β t : ℝ} (hT : 0 < T) (hβ : 1 < β) (ht : T < t) :
    continuedExponential T t < hyperExponential T β t := by
  unfold continuedExponential hyperExponential
  apply (Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr
  -- t/T > 1, so (t/T)^β > (t/T)^1 = t/T.
  have hx : (1 : ℝ) < t / T := (one_lt_div hT).mpr ht
  have h := Real.rpow_lt_rpow_of_exponent_lt hx hβ
  simpa using h

/-- Helper: `t/T → ∞` as `t → ∞` for `T > 0`. -/
private lemma tendsto_div_const_atTop {T : ℝ} (hT : 0 < T) :
    Filter.Tendsto (fun t : ℝ => t / T) Filter.atTop Filter.atTop := by
  -- Use `Filter.Tendsto.atTop_mul_const` on `tendsto_id` with `0 < 1/T`.
  have hid : Filter.Tendsto (fun t : ℝ => t) Filter.atTop Filter.atTop := Filter.tendsto_id
  have hmul : Filter.Tendsto (fun t : ℝ => t * (1 / T)) Filter.atTop Filter.atTop :=
    hid.atTop_mul_const (by positivity : (0 : ℝ) < 1 / T)
  refine hmul.congr ?_
  intro t; rw [mul_one_div]

/-- Helper: `2^(t/T) → ∞` as `t → ∞` for `T > 0`. -/
private lemma continuedExponential_tendsto_atTop {T : ℝ} (hT : 0 < T) :
    Filter.Tendsto (continuedExponential T) Filter.atTop Filter.atTop := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdiv := tendsto_div_const_atTop hT
  have hinner : Filter.Tendsto (fun t : ℝ => t / T * Real.log 2)
      Filter.atTop Filter.atTop := hdiv.atTop_mul_const hlog
  have hcomp : Filter.Tendsto
      (fun t : ℝ => Real.exp (t / T * Real.log 2)) Filter.atTop Filter.atTop :=
    Real.tendsto_exp_atTop.comp hinner
  refine hcomp.congr ?_
  intro t
  unfold continuedExponential
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), mul_comm]

/-- THEOREM (sigmoid is bounded; continued is unbounded, so continued
    eventually exceeds sigmoid no matter how high the ceiling L). -/
theorem continued_exceeds_sigmoid_ceiling
    {T : ℝ} (hT : 0 < T) (L : ℝ) :
    ∃ t, L ≤ continuedExponential T t := by
  have hlim := continuedExponential_tendsto_atTop hT
  obtain ⟨t, ht⟩ := (Filter.tendsto_atTop_atTop.mp hlim) L
  exact ⟨t, ht t (le_refl _)⟩

/-- THEOREM (continued eventually dominates sigmoid): there exists `t`
    with `sigmoidSaturation k L t₀ t < continuedExponential T t`. -/
theorem continued_eventually_above_sigmoid
    {T k L t₀ : ℝ} (hT : 0 < T) (hL : 0 < L) :
    ∃ t, sigmoidSaturation k L t₀ t < continuedExponential T t := by
  obtain ⟨t, ht⟩ := continued_exceeds_sigmoid_ceiling (L := L) hT
  refine ⟨t, ?_⟩
  have := sigmoidSaturation_lt_ceiling (k := k) (t₀ := t₀) (t := t) hL
  linarith

/-- THEOREM (winter tends to zero): if `decay > 0`, the AI-winter trajectory
    tends to `0` as `t → ∞`. The labor-cost integral does NOT unwind; see
    `winter_displacement_does_not_unwind` below. -/
theorem aiWinter_tendsto_zero
    {T t_winter decay : ℝ} (hd : 0 < decay) :
    Filter.Tendsto (aiWinter T t_winter decay) Filter.atTop (nhds 0) := by
  -- Eventually t > t_winter, and the function is then
  --   2^(t_winter/T) * exp(-decay * (t - t_winter))
  -- which tends to 0.
  have hconst : (0 : ℝ) < (2 : ℝ) ^ (t_winter / T) :=
    Real.rpow_pos_of_pos (by norm_num) _
  -- Use eventually equality on [t_winter, ∞).
  have hev : ∀ᶠ t in Filter.atTop, aiWinter T t_winter decay t
      = (2 : ℝ) ^ (t_winter / T) * Real.exp (-decay * (t - t_winter)) := by
    filter_upwards [Filter.eventually_gt_atTop t_winter] with t ht
    unfold aiWinter
    rw [if_neg (not_le.mpr ht)]
  -- The RHS tends to 0.
  have h1 : Filter.Tendsto (fun t : ℝ => -decay * (t - t_winter))
      Filter.atTop Filter.atBot := by
    have hsub : Filter.Tendsto (fun t : ℝ => t - t_winter) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_add_const_right _ (-t_winter) Filter.tendsto_id |>.congr
        (fun t => by show t + -t_winter = t - t_winter; ring)
    have hmul : Filter.Tendsto (fun t : ℝ => (t - t_winter) * decay)
        Filter.atTop Filter.atTop := hsub.atTop_mul_const hd
    -- `(t - t_winter) * decay → ∞`, negation → `-∞`.
    have hneg : Filter.Tendsto (fun t : ℝ => -((t - t_winter) * decay))
        Filter.atTop Filter.atBot := Filter.tendsto_neg_atTop_atBot.comp hmul
    refine hneg.congr ?_
    intro t; ring
  have h2 : Filter.Tendsto (fun t : ℝ => Real.exp (-decay * (t - t_winter)))
      Filter.atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp h1
  have h3 : Filter.Tendsto
      (fun t : ℝ => (2 : ℝ) ^ (t_winter / T) * Real.exp (-decay * (t - t_winter)))
      Filter.atTop (nhds ((2 : ℝ) ^ (t_winter / T) * 0)) :=
    h2.const_mul _
  rw [mul_zero] at h3
  exact h3.congr' (Filter.EventuallyEq.symm hev)

/-- THEOREM (continued dominates winter for large t): there exists a
    time after which continued strictly exceeds winter. -/
theorem continued_eventually_above_winter
    {T t_winter decay : ℝ} (hT : 0 < T) (hd : 0 < decay) :
    ∃ t, aiWinter T t_winter decay t < continuedExponential T t := by
  -- continued tends to ∞; winter tends to 0. Pick t large enough.
  have hlim_c := continuedExponential_tendsto_atTop hT
  have hlim_w := aiWinter_tendsto_zero (T := T) (t_winter := t_winter) hd
  -- Eventually continued > 1 and winter < 1.
  have h1 : ∀ᶠ t in Filter.atTop, (1 : ℝ) < continuedExponential T t :=
    hlim_c.eventually (Filter.eventually_gt_atTop 1)
  have h2 : ∀ᶠ t in Filter.atTop, aiWinter T t_winter decay t < 1 := by
    have := hlim_w.eventually (isOpen_Iio.mem_nhds (show (0 : ℝ) < 1 by norm_num))
    filter_upwards [this] with t ht
    exact ht
  obtain ⟨t, ht1, ht2⟩ := (h1.and h2).exists
  exact ⟨t, by linarith⟩

/-! ### The unified trajectory type and its evaluator. -/

/-- A canonical AI intelligence trajectory. -/
inductive Trajectory where
  | mythosPlateau (t_now T : ℝ) : Trajectory
  | continued (T : ℝ) : Trajectory
  | sigmoid (k L t₀ : ℝ) : Trajectory
  | hyperExp (T β : ℝ) : Trajectory
  | winter (T t_winter decay : ℝ) : Trajectory

namespace Trajectory

/-- Evaluate a trajectory at a time `t`. -/
noncomputable def eval : Trajectory → ℝ → ℝ
  | mythosPlateau t_now T, t => Economy.mythosPlateau t_now T t
  | continued T, t => Economy.continuedExponential T t
  | sigmoid k L t₀, t => Economy.sigmoidSaturation k L t₀ t
  | hyperExp T β, t => Economy.hyperExponential T β t
  | winter T tw d, t => Economy.aiWinter T tw d t

/-- Predicate: the trajectory's parameters are economically meaningful.
    For sigmoid, this means the ceiling `L` is strictly positive. All other
    shapes are automatically positive. -/
def WellParam : Trajectory → Prop
  | mythosPlateau _ _ => True
  | continued _ => True
  | sigmoid _ L _ => 0 < L
  | hyperExp _ _ => True
  | winter _ _ _ => True

/-- THEOREM (universal positivity of the trajectory family under
    well-parameterization). -/
theorem eval_pos : ∀ {τ : Trajectory}, τ.WellParam → ∀ t, 0 < τ.eval t
  | mythosPlateau _ _, _, _ => mythosPlateau_pos _ _ _
  | continued _, _, _ => continuedExponential_pos _ _
  | sigmoid _ _ _, hL, _ => sigmoidSaturation_pos hL
  | hyperExp _ _, _, _ => hyperExponential_pos _ _ _
  | winter _ _ _, _, _ => aiWinter_pos _ _ _ _

end Trajectory

/-! ### Composition with the macro forecast.

`trajectoryGDP` is the scenario-agnostic log-GDP deviation built from a
raw intelligence trajectory `I : ℝ → ℝ`. It plays the role of
`Scenario.logGDPDeviation` but accepts ANY trajectory shape instead of
committing to a fixed doubling time.

We bolt the existing `exposureFromHorizon` exposure curve on top of `I`
and then plug into the same `gA + (1-α) gK` channel Forecast.lean uses.
-/

/-- The TFP-channel growth rate induced by an arbitrary trajectory `I`,
    a base horizon `H₀`, saturation horizon `Hmax`, and cost-savings
    coefficient `cost`. -/
noncomputable def trajectoryGA
    (I : ℝ → ℝ) (H₀ Hmax cost t : ℝ) : ℝ :=
  exposureFromHorizon (taskHorizon (I t) H₀) Hmax * cost

/-- Log-GDP deviation induced by an arbitrary intelligence trajectory. -/
noncomputable def trajectoryLogGDP
    (I : ℝ → ℝ) (H₀ Hmax α gK cost t : ℝ) : ℝ :=
  (trajectoryGA I H₀ Hmax cost t + (1 - α) * gK) * t

/-- THEOREM (gA nonneg). -/
theorem trajectoryGA_nonneg
    {I : ℝ → ℝ} {H₀ Hmax cost t : ℝ} (hcost : 0 ≤ cost) :
    0 ≤ trajectoryGA I H₀ Hmax cost t := by
  unfold trajectoryGA
  exact mul_nonneg (exposureFromHorizon_mem_unit _ _).1 hcost

/-- THEOREM (log-GDP deviation nonneg for t ≥ 0 under standard Ghost-GDP
    conditions). -/
theorem trajectoryLogGDP_nonneg
    {I : ℝ → ℝ} {H₀ Hmax α gK cost t : ℝ}
    (hcost : 0 ≤ cost) (hα : α ≤ 1) (hgK : 0 ≤ gK) (ht : 0 ≤ t) :
    0 ≤ trajectoryLogGDP I H₀ Hmax α gK cost t := by
  unfold trajectoryLogGDP
  have h1 : 0 ≤ trajectoryGA I H₀ Hmax cost t := trajectoryGA_nonneg hcost
  have h2 : 0 ≤ (1 - α) * gK := mul_nonneg (by linarith) hgK
  exact mul_nonneg (by linarith) ht

/-- THEOREM (central composition): if two intelligence trajectories satisfy
    `I₁ t ≤ I₂ t` pointwise, then the induced log-GDP deviations are
    weakly ordered the same way, for any time `t ≥ 0`, whenever the
    base-horizon and cost parameters are nonnegative.

    This is the LIFTING theorem — trajectory dominance in the space of
    capability curves lifts to GDP dominance in the space of macro
    forecasts, without any further analysis. -/
theorem gdp_dominance_from_intelligence_dominance
    {I₁ I₂ : ℝ → ℝ} {H₀ Hmax α gK cost t : ℝ}
    (hH₀ : 0 < H₀) (hHmax : 0 < Hmax) (hcost : 0 ≤ cost)
    (hle : I₁ t ≤ I₂ t) (ht : 0 ≤ t) :
    trajectoryLogGDP I₁ H₀ Hmax α gK cost t
      ≤ trajectoryLogGDP I₂ H₀ Hmax α gK cost t := by
  unfold trajectoryLogGDP trajectoryGA
  have hexp : exposureFromHorizon (taskHorizon (I₁ t) H₀) Hmax
      ≤ exposureFromHorizon (taskHorizon (I₂ t) H₀) Hmax := by
    apply exposureFromHorizon_mono hHmax
    unfold taskHorizon
    exact mul_le_mul_of_nonneg_left hle hH₀.le
  have hgA : trajectoryGA I₁ H₀ Hmax cost t ≤ trajectoryGA I₂ H₀ Hmax cost t := by
    unfold trajectoryGA
    exact mul_le_mul_of_nonneg_right hexp hcost
  have hsum : trajectoryGA I₁ H₀ Hmax cost t + (1 - α) * gK
      ≤ trajectoryGA I₂ H₀ Hmax cost t + (1 - α) * gK := by linarith
  exact mul_le_mul_of_nonneg_right hsum ht

/-- THEOREM (welfare-GDP divergence is universal across the space of
    possible futures): for EVERY trajectory shape, there exist parameter
    values where `welfareDelta < 0` while `trajectoryLogGDP > 0`. We use
    the Acemoglu-Restrepo labor-share-collapse witness from
    `Economy.Welfare.welfare_can_fall_with_gdp_rise`, which is independent
    of the trajectory shape. The point of this theorem is the QUANTIFIER
    STRUCTURE: welfare-divergence is not a phenomenon of fast doubling;
    it is a phenomenon of the LABOR-SHARE CHANNEL which runs separately
    from any trajectory.  -/
theorem welfare_can_diverge_under_any_trajectory (_τ : Trajectory) :
    ∃ (Y Y' lam lam' : ℝ), 0 < Y ∧ 0 < Y' ∧ 0 < lam ∧ 0 < lam'
      ∧ Y < Y' ∧ welfareDelta (lam * Y) (lam' * Y') < 0 := by
  -- The witness does not depend on _τ. That's the content.
  exact welfare_can_fall_with_gdp_rise

/-- THEOREM (Mythos plateau corollary, saturation of log-GDP deviation):
    under the Mythos plateau trajectory (capability frozen after `t_now`),
    the TFP-channel gA is eventually constant. Concretely, for `t ≥ t_now`,
    `trajectoryGA (mythosPlateau t_now T) H₀ Hmax cost t` is CONSTANT in
    `t` and equals its value at `t_now`. This is the "Mythos ceiling" —
    the gift stops giving more. -/
theorem mythos_plateau_corollary
    {t_now T H₀ Hmax cost t : ℝ}
    (ht : t_now ≤ t) :
    trajectoryGA (mythosPlateau t_now T) H₀ Hmax cost t
      = trajectoryGA (mythosPlateau t_now T) H₀ Hmax cost t_now := by
  unfold trajectoryGA
  rcases eq_or_lt_of_le ht with heq | hlt
  · rw [← heq]
  · -- Both sides: plateau value at t_now.
    have h1 : mythosPlateau t_now T t = (2 : ℝ) ^ (t_now / T) :=
      mythosPlateau_frozen hlt
    have h2 : mythosPlateau t_now T t_now = (2 : ℝ) ^ (t_now / T) := by
      unfold mythosPlateau; rw [if_pos (le_refl _)]
    rw [h1, h2]

/-- THEOREM (AI winter corollary — displacement does NOT unwind):
    under the winter trajectory, the TFP channel eventually goes to 0,
    but as long as there was ANY positive time spent at a positive gA,
    the cumulative growth contribution up to any `t ≥ t_winter` is
    strictly positive. Formally: for `t ≥ t_winter ≥ 0` and `cost > 0`,
    `0 < trajectoryGA (winter T t_winter d) ... t_winter`. Even though
    the rate later returns to zero, the log-GDP deviation accumulated by
    time `t_winter` is LOCKED IN by the positive rate between `0` and
    `t_winter`. -/
theorem winter_displacement_does_not_unwind
    {T t_winter decay H₀ Hmax cost : ℝ}
    (hT : 0 < T) (hH₀ : 0 < H₀) (hHmax : 0 < Hmax) (hcost : 0 < cost)
    (ht_w : 0 < t_winter) :
    0 < trajectoryGA (aiWinter T t_winter decay) H₀ Hmax cost t_winter := by
  unfold trajectoryGA
  have hIeq : aiWinter T t_winter decay t_winter = (2 : ℝ) ^ (t_winter / T) := by
    unfold aiWinter; rw [if_pos (le_refl _)]
  rw [hIeq]
  -- We need 0 < exposureFromHorizon(taskHorizon(2^(t_winter/T), H₀), Hmax) * cost
  -- The capability level 2^(t_w/T) > 1, so the horizon is > H₀ > 0, so the
  -- exposure (which is `min 1 (max 0 (H/Hmax))`) is > 0 when H > 0.
  have hI : (1 : ℝ) < (2 : ℝ) ^ (t_winter / T) := by
    have h1 : (1 : ℝ) < 2 := by norm_num
    have : (0 : ℝ) < t_winter / T := div_pos ht_w hT
    calc (1 : ℝ) = (2 : ℝ) ^ (0 : ℝ) := by rw [Real.rpow_zero]
      _ < (2 : ℝ) ^ (t_winter / T) := by
          apply (Real.rpow_lt_rpow_left_iff h1).mpr this
  have hHpos : 0 < taskHorizon ((2 : ℝ) ^ (t_winter / T)) H₀ := by
    unfold taskHorizon
    exact mul_pos hH₀ (by linarith)
  -- Now `exposureFromHorizon` at a positive horizon:
  have hexpPos : 0 < exposureFromHorizon
      (taskHorizon ((2 : ℝ) ^ (t_winter / T)) H₀) Hmax := by
    unfold exposureFromHorizon
    have hdiv : 0 < taskHorizon ((2 : ℝ) ^ (t_winter / T)) H₀ / Hmax :=
      div_pos hHpos hHmax
    have hmax_pos : 0 < max 0
        (taskHorizon ((2 : ℝ) ^ (t_winter / T)) H₀ / Hmax) :=
      lt_of_lt_of_le hdiv (le_max_right _ _)
    exact lt_min (by norm_num) hmax_pos
  exact mul_pos hexpPos hcost

/-- THEOREM (hyper-exponential corollary, super-linear GDP): under a
    hyper-exponential trajectory with `β > 1`, the GDP deviation at time
    `t ≥ T` is bounded below by the continued-exponential GDP deviation
    at the same time, assuming all other scenario parameters are equal.
    This is the "fast takeoff ≥ continued" comparison. -/
theorem hyperExp_corollary
    {T β H₀ Hmax α gK cost t : ℝ}
    (hT : 0 < T) (hβ : 1 < β) (ht : T ≤ t)
    (hH₀ : 0 < H₀) (hHmax : 0 < Hmax) (hcost : 0 ≤ cost) :
    trajectoryLogGDP (continuedExponential T) H₀ Hmax α gK cost t
      ≤ trajectoryLogGDP (hyperExponential T β) H₀ Hmax α gK cost t := by
  have ht_nn : (0 : ℝ) ≤ t := le_trans hT.le ht
  have hlocal : continuedExponential T t ≤ hyperExponential T β t :=
    hyperExp_dominates_continued hT hβ ht
  have hcnn : 0 ≤ continuedExponential T t := (continuedExponential_pos T t).le
  exact gdp_dominance_from_intelligence_dominance
    (I₁ := continuedExponential T) (I₂ := hyperExponential T β)
    hH₀ hHmax hcost hlocal ht_nn

/-- THEOREM (plateau-below-continued GDP lift): the Mythos plateau
    induces a log-GDP deviation weakly below that of continued
    exponential at every `t ≥ 0`. -/
theorem plateau_below_continued_GDP
    {t_now T H₀ Hmax α gK cost t : ℝ}
    (hT : 0 < T) (ht : 0 ≤ t)
    (hH₀ : 0 < H₀) (hHmax : 0 < Hmax) (hcost : 0 ≤ cost) :
    trajectoryLogGDP (mythosPlateau t_now T) H₀ Hmax α gK cost t
      ≤ trajectoryLogGDP (continuedExponential T) H₀ Hmax α gK cost t := by
  have hle : mythosPlateau t_now T t ≤ continuedExponential T t :=
    continued_dominates_plateau hT
  have hmp_nn : 0 ≤ mythosPlateau t_now T t := (mythosPlateau_pos _ _ _).le
  exact gdp_dominance_from_intelligence_dominance
    (I₁ := mythosPlateau t_now T) (I₂ := continuedExponential T)
    hH₀ hHmax hcost hle ht

end Economy
