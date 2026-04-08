/-
  Economy.Inequality
  Distributional consequences: capital share ↔ top-decile income share.

  ECONOMIC CLAIM: If the population is split into capital-owners (share ψ of
  capital, fraction ν of population) and labor, and total output is
  `Y = wL + rK`, then the capital share `rK/Y` is a linear map from
  α (the Cobb-Douglas capital share) to individual-level income shares.
  If capital share rises by δ, top-decile income share rises by at most
  `δ · ψ_top` where `ψ_top` is the top decile's capital ownership share.

  SOURCES:
  * Piketty (2014), "Capital in the Twenty-First Century", Ch. 7–8.
  * Autor (2019), "Work of the Past, Work of the Future", AEA Papers 109: 1–32.
  * Zucman (2019), "Global Wealth Inequality", Annual Review 11: 109–138.

  TIER: THEOREM for linear bounds; we do NOT formalize Gini-from-Finset here
  (that needs Lebesgue integration machinery for the general case and adds
  many lines without changing the economic conclusion). The two-class version
  below suffices for the top-decile-share result.
-/
import Mathlib.Tactic

namespace Economy

/-- Two-class economy: capital owners own share `ψ_k` of capital, the rest is
    uniform labor income. Population fractions are `ν_k` and `1 - ν_k`. -/
structure TwoClass where
  α : ℝ           -- capital share of output
  ψ_k : ℝ         -- top-decile capital ownership share (≈ 0.77 US)
  ν_k : ℝ         -- top-decile population share (0.1)
  Y : ℝ           -- total output
  α_nn : 0 ≤ α
  α_le_one : α ≤ 1
  ψ_nn : 0 ≤ ψ_k
  ψ_le_one : ψ_k ≤ 1
  ν_nn : 0 ≤ ν_k
  ν_le_one : ν_k ≤ 1
  Y_pos : 0 < Y

namespace TwoClass

/-- Top-decile income = capital share × ownership share × output + labor share × population share × output. -/
noncomputable def topDecileIncome (t : TwoClass) : ℝ :=
  t.α * t.ψ_k * t.Y + (1 - t.α) * t.ν_k * t.Y

/-- Top-decile income share. -/
noncomputable def topDecileShare (t : TwoClass) : ℝ :=
  t.topDecileIncome / t.Y

/-- THEOREM: top-decile income share is in [0,1]. -/
theorem topDecileShare_mem_unit (t : TwoClass) :
    0 ≤ t.topDecileShare ∧ t.topDecileShare ≤ 1 := by
  unfold topDecileShare topDecileIncome
  refine ⟨?_, ?_⟩
  · apply div_nonneg _ t.Y_pos.le
    have h1 : 0 ≤ t.α * t.ψ_k * t.Y :=
      mul_nonneg (mul_nonneg t.α_nn t.ψ_nn) t.Y_pos.le
    have h2 : 0 ≤ (1 - t.α) * t.ν_k * t.Y := by
      apply mul_nonneg (mul_nonneg (by linarith [t.α_le_one]) t.ν_nn) t.Y_pos.le
    linarith
  · rw [div_le_one t.Y_pos]
    have h1 : t.α * t.ψ_k * t.Y ≤ t.α * 1 * t.Y := by
      apply mul_le_mul_of_nonneg_right _ t.Y_pos.le
      exact mul_le_mul_of_nonneg_left t.ψ_le_one t.α_nn
    have h2 : (1 - t.α) * t.ν_k * t.Y ≤ (1 - t.α) * 1 * t.Y := by
      apply mul_le_mul_of_nonneg_right _ t.Y_pos.le
      exact mul_le_mul_of_nonneg_left t.ν_le_one (by linarith [t.α_le_one])
    nlinarith

/-- THEOREM (top-decile share rises when capital share rises, at fixed ψ_k > ν_k):
    if the top-decile's capital ownership share exceeds its population share
    (i.e., they are over-represented in capital ownership, which is empirically
    the case: ψ_k ≈ 0.77, ν_k = 0.10), then raising α raises the top-decile
    income share. -/
theorem topDecile_rises_with_capital_share (t t' : TwoClass)
    (hY : t.Y = t'.Y) (hψ : t.ψ_k = t'.ψ_k) (hν : t.ν_k = t'.ν_k)
    (hov : t.ν_k < t.ψ_k) (hα : t.α ≤ t'.α) :
    t.topDecileShare ≤ t'.topDecileShare := by
  unfold topDecileShare topDecileIncome
  rw [hY, hψ, hν]
  apply (div_le_div_iff_of_pos_right t'.Y_pos).mpr
  have hY' : 0 < t'.Y := t'.Y_pos
  have hdiff : t'.α * t'.ψ_k * t'.Y + (1 - t'.α) * t'.ν_k * t'.Y
             - (t.α * t'.ψ_k * t'.Y + (1 - t.α) * t'.ν_k * t'.Y)
             = (t'.α - t.α) * (t'.ψ_k - t'.ν_k) * t'.Y := by ring
  have hpos : 0 ≤ (t'.α - t.α) * (t'.ψ_k - t'.ν_k) * t'.Y := by
    apply mul_nonneg
    · apply mul_nonneg
      · linarith
      · have : t.ν_k < t.ψ_k := hov
        rw [hψ, hν] at this; linarith
    · exact hY'.le
  linarith

/-- THEOREM (linear bound on top-decile share change): if α rises by δ,
    the top-decile share rises by at most `δ · ψ_k` (the overrepresentation
    upper bound). This is the Piketty-Saez linear bound in two-class form. -/
theorem topDecile_linear_bound (t t' : TwoClass)
    (hY : t.Y = t'.Y) (hψ : t.ψ_k = t'.ψ_k) (hν : t.ν_k = t'.ν_k) :
    t'.topDecileShare - t.topDecileShare
      = (t'.α - t.α) * (t'.ψ_k - t'.ν_k) := by
  unfold topDecileShare topDecileIncome
  rw [hY, hψ, hν]
  have hY' : t'.Y ≠ 0 := ne_of_gt t'.Y_pos
  field_simp
  ring

end TwoClass

end Economy
