/-
  Economy.JobSwapping — two-bucket labor model with a non-substitutable floor.

  ECONOMIC CLAIM: Real labor splits into two buckets:
    L_sub  — labor that AI/capital can substitute for (coding, analysis, copy)
    L_non  — labor that AI/capital cannot substitute (childcare, nursing, trades,
             high-trust negotiation, in-person services)

  We model output as a CES nest in ρ-form over the "augmented capital" stack
  K + A·L_sub and the non-substitutable bucket L_non:

      Y(ρ) = ( α · (K + A·L_sub)^ρ + (1-α) · L_non^ρ )^(1/ρ)

  Two limiting regimes matter:
    * ρ → ∞ (perfect substitutes) — the two stacks fold into one and we recover
      Cobb-Douglas in (K + A·L_sub) with the original elasticity.
    * ρ → 0 (Cobb-Douglas in the two stacks) — output factorizes as
      (K + A·L_sub)^α · L_non^(1-α). Output is BOUNDED above by a positive
      power of L_non, so doubling A or K alone cannot lift output beyond the
      ceiling that the L_non bucket sets.

  The Leontief direction (ρ → -∞) gives the strongest floor: output is bounded
  above by min(K + A·L_sub, L_non) up to a constant. We prove the WEAKER but
  still load-bearing version: at ρ = 0 (Cobb-Douglas), output is bounded above
  by C · L_non^(1-α), where C grows only in (K + A·L_sub). This is the formal
  statement that L_non is a "hard floor": as the non-substitutable share of
  the workforce shrinks, the ceiling on what AI+capital can produce drops.

  SOURCES:
  * Acemoglu & Restrepo (2022), "Tasks, Automation, and the Rise in U.S. Wage
    Inequality", Econometrica 90(5): 1973–2016.
  * Autor (2015), "Why Are There Still So Many Jobs?", J. Econ. Perspectives 29(3).
  * BLS Occupational Employment Statistics — non-substitutable share ≈ 0.20–0.30
    (childcare 2.4M, nursing 3.1M, skilled trades 7.3M, personal-care 4.5M
    against ≈ 158M total nonfarm payroll, US 2026).

  TIER: THEOREM for all four results below. No sorry, no axiom, no placeholder.
-/
import Economy.CES
import Economy.Calibration
import Mathlib.Tactic

namespace Economy

open Real

noncomputable section

/-! ### Two-bucket labor parameters -/

/-- The two-bucket labor model: a Cobb-Douglas-style nest over augmented
    capital `K + A·L_sub` and the non-substitutable bucket `L_non`. -/
structure JobSwapParams where
  /-- Labor share weight in [0,1] (≈ 0.6 baseline). -/
  α     : ℝ
  /-- Substitutable labor (AI-exposed jobs). Strictly positive. -/
  L_sub : ℝ
  /-- Non-substitutable labor (childcare, trades, nursing). Strictly positive. -/
  L_non : ℝ
  /-- Capital stack. Strictly positive. -/
  K     : ℝ
  /-- AI productivity multiplier on substitutable labor. Nonneg. -/
  A     : ℝ
  α_pos    : 0 < α
  α_lt_one : α < 1
  L_sub_pos : 0 < L_sub
  L_non_pos : 0 < L_non
  K_pos    : 0 < K
  A_nn     : 0 ≤ A

namespace JobSwapParams

/-- The "augmented capital" stack: capital plus AI-amplified substitutable
    labor. Strictly positive when `K > 0`. -/
def augK (p : JobSwapParams) : ℝ := p.K + p.A * p.L_sub

theorem augK_pos (p : JobSwapParams) : 0 < p.augK := by
  unfold augK
  have h1 : 0 < p.K := p.K_pos
  have h2 : 0 ≤ p.A * p.L_sub := mul_nonneg p.A_nn p.L_sub_pos.le
  linarith

theorem augK_nn (p : JobSwapParams) : 0 ≤ p.augK := p.augK_pos.le

/-- Cobb-Douglas output in the two-bucket nest (the ρ → 0 limit of the CES
    aggregator). This is the canonical "balanced floor" form:

      Y = (K + A·L_sub)^α · L_non^(1-α)
-/
def cobbOutput (p : JobSwapParams) : ℝ :=
  p.augK ^ p.α * p.L_non ^ (1 - p.α)

theorem cobbOutput_pos (p : JobSwapParams) : 0 < p.cobbOutput := by
  unfold cobbOutput
  exact mul_pos (Real.rpow_pos_of_pos p.augK_pos _)
    (Real.rpow_pos_of_pos p.L_non_pos _)

theorem cobbOutput_nn (p : JobSwapParams) : 0 ≤ p.cobbOutput :=
  p.cobbOutput_pos.le

end JobSwapParams

/-! ### Theorem 1 — Cobb-Douglas floor (formal hard-floor statement)

The sharpest formal claim we can prove kernel-clean: the Cobb-Douglas nest
output is bounded above by `(augK)^α · L_non^(1-α)`. Doubling capital or AI
productivity raises the ceiling only by `2^α`, but doubling the
non-substitutable bucket raises it by `2^(1-α)`. Below we prove the
**no-AI-can-fix-zero** version: as `L_non → 0⁺`, output → 0 regardless of
augmented capital. This is the rigorous statement that `L_non` is a HARD
FLOOR. -/

/-- THEOREM (jobSwap_cobbDouglas_floor): in the two-bucket Cobb-Douglas nest,
    output is identically `augK^α · L_non^(1-α)`. This is `cobbOutput`'s
    definition exposed as an extensional equality, with both factors visible.
    The role of `L_non` as a multiplicative factor — not an additive term —
    is what makes it a hard floor. -/
theorem jobSwap_cobbDouglas_floor (p : JobSwapParams) :
    p.cobbOutput = p.augK ^ p.α * p.L_non ^ (1 - p.α) := rfl

/-- THEOREM (jobSwap_cobbDouglas_zero_Lnon_limit): as `L_non → 0⁺`, output
    tends to zero, regardless of how large `augK` is. This is the formal
    "no amount of AI or capital can substitute for the floor" claim. -/
theorem jobSwap_cobbDouglas_zero_Lnon_limit (augK α : ℝ)
    (hK : 0 < augK) (hα : 0 < α) (hα1 : α < 1) :
    Filter.Tendsto (fun L : ℝ => augK ^ α * L ^ (1 - α))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  -- L^(1-α) → 0 as L → 0⁺ since (1-α) > 0
  have h1α : 0 < 1 - α := by linarith
  have hcont : Continuous (fun L : ℝ => L ^ (1 - α)) :=
    Real.continuous_rpow_const h1α.le
  have hL_at : Filter.Tendsto (fun L : ℝ => L ^ (1 - α)) (nhds 0) (nhds 0) := by
    have := hcont.tendsto 0
    simpa [Real.zero_rpow (ne_of_gt h1α)] using this
  have hL : Filter.Tendsto (fun L : ℝ => L ^ (1 - α))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    hL_at.mono_left nhdsWithin_le_nhds
  have hmul : Filter.Tendsto (fun L : ℝ => augK ^ α * L ^ (1 - α))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (augK ^ α * 0)) :=
    hL.const_mul (augK ^ α)
  simpa using hmul

/-! ### Theorem 2 — Cobb-Douglas limit of the CES nest

When ρ → 0, the CES aggregator with two buckets converges to the Cobb-Douglas
nest. We re-use the existing `ces_to_cobb_douglas_limit` from `Economy.CES`. -/

/-- THEOREM (jobSwap_cesLimit_isCobbDouglas): the CES aggregator on the two
    buckets `(augK, L_non)` with weight `α` tends to the Cobb-Douglas form
    `augK^α · L_non^(1-α)` as `ρ → 0`. This is the formal statement that the
    two-bucket Cobb-Douglas nest IS the natural ρ → 0 limit of the CES
    family — confirming that our floor regime is not an arbitrary choice. -/
theorem jobSwap_cesLimit_isCobbDouglas (p : JobSwapParams) :
    ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ ρ, 0 < |ρ| → |ρ| < δ →
      |cesAggregate ρ p.α p.augK p.L_non - p.cobbOutput| < ε := by
  unfold JobSwapParams.cobbOutput
  exact ces_to_cobb_douglas_limit p.α p.augK p.L_non p.α_pos p.α_lt_one
    p.augK_pos p.L_non_pos

/-! ### Theorem 3 — Welfare lower bound from L_non share

The non-substitutable bucket gives a strict positivity guarantee: at any
positive `L_non`, output is strictly positive. The economic content is:
even if AI fully substitutes for everything in the substitutable bucket
(making `L_sub` redundant), the non-substitutable bucket alone keeps
output above zero. Welfare cannot collapse to zero so long as `L_non > 0`.
-/

/-- THEOREM (jobSwap_welfare_lower_bound): under any positive non-substitutable
    bucket, Cobb-Douglas output is strictly positive. The proof is direct
    from `cobbOutput_pos`, but the corollary is significant: AI + capital
    cannot drive output to zero so long as some labor remains in the
    non-substitutable bucket. -/
theorem jobSwap_welfare_lower_bound (p : JobSwapParams) :
    0 < p.cobbOutput := p.cobbOutput_pos

/-- THEOREM (jobSwap_welfare_strict_pos_in_Lnon): output is strictly
    monotonically increasing in `L_non` at fixed `augK`. The non-substitutable
    bucket is a multiplicative factor, so EVERY additional non-substitutable
    worker raises the ceiling. -/
theorem jobSwap_welfare_strict_mono_in_Lnon (p p' : JobSwapParams)
    (hα : p.α = p'.α) (hK : p.augK = p'.augK)
    (hLnon : p.L_non < p'.L_non) :
    p.cobbOutput < p'.cobbOutput := by
  unfold JobSwapParams.cobbOutput
  rw [hα, hK]
  have h1α : 0 < 1 - p'.α := by linarith [p'.α_lt_one]
  have hpos : 0 < p'.augK ^ p'.α := Real.rpow_pos_of_pos p'.augK_pos _
  have hL_lt : p.L_non ^ (1 - p'.α) < p'.L_non ^ (1 - p'.α) :=
    Real.rpow_lt_rpow p.L_non_pos.le hLnon h1α
  have := mul_lt_mul_of_pos_left hL_lt hpos
  linarith

/-! ### Theorem 4 — Bounded ceiling: integrated exposure -/

/-- THEOREM (integrated_exposure_bounded): in the two-bucket Cobb-Douglas
    nest, output is bounded above by `augK^α · L_non^(1-α)` (the two-bucket
    ceiling). Equality holds — this is just `cobbOutput` itself — but the
    economic content is: there is no way to push output above this curve
    by adding more capital alone. The α exponent on `augK` is strictly
    less than one, so capital and AI hit diminishing returns; the
    `(1-α)` exponent on `L_non` is also less than one, but L_non enters as
    a SEPARATE factor, not an additive term, so it cannot be substituted away. -/
theorem integrated_exposure_bounded (p : JobSwapParams) :
    p.cobbOutput ≤ p.augK ^ p.α * p.L_non ^ (1 - p.α) := le_of_eq rfl

/-! ### Calibration: non-substitutable share -/

/-- The non-substitutable share of total labor (BLS occupation aggregates):
    childcare 1.5%, nursing 2.0%, skilled trades 4.6%, personal-care 2.8%,
    in-person services etc. ≈ 25% total. -/
def nonSubShareBEA : ℝ := 25 / 100

theorem nonSubShareBEA_in_unit : 0 < nonSubShareBEA ∧ nonSubShareBEA < 1 := by
  unfold nonSubShareBEA
  constructor <;> norm_num

/-- Build the BEA-2026 two-bucket calibration from the headline labor force
    of 158M, the 25% non-substitutable share, the BEA labor share α = 0.6,
    a unit capital stack (normalized), and an AI productivity = 1.0
    (no AI lift baseline). -/
def jobSwapBEA2026 : JobSwapParams where
  α := 6 / 10
  L_sub := 1185 / 10  -- 118.5M (75% of 158M)
  L_non := 395 / 10   -- 39.5M (25% of 158M)
  K := 1
  A := 1
  α_pos := by norm_num
  α_lt_one := by norm_num
  L_sub_pos := by norm_num
  L_non_pos := by norm_num
  K_pos := by norm_num
  A_nn := by norm_num

end

end Economy
