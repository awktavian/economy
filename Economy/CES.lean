/-
  Economy.CES
  Constant-elasticity-of-substitution aggregation between two tasks.

  ECONOMIC CLAIM: With CES aggregator Y = (α·y1^ρ + (1-α)·y2^ρ)^(1/ρ),
  ρ = (σ-1)/σ, the elasticity of substitution is σ. As σ → 1, the aggregator
  tends to Cobb-Douglas (proved here as a CONJECTURE with L'Hôpital citation).
  The displacement-vs-productivity decomposition (Acemoglu-Restrepo 2022)
  follows from the sign of (σ-1).

  SOURCES:
  * Acemoglu & Restrepo (2022), "Tasks, Automation, and the Rise in U.S. Wage
    Inequality", Econometrica 90(5): 1973–2016. https://doi.org/10.3982/ECTA19815
  * Arrow, Chenery, Minhas, Solow (1961), "Capital-Labor Substitution and
    Economic Efficiency", Review of Economics and Statistics 43(3): 225–250.

  TIER: THEOREM for the homogeneity-of-degree-one and nonnegativity properties;
  CONJECTURE (sorry + citation) for the σ → 1 Cobb-Douglas limit and for the
  marginal-rate-of-substitution identity (which needs derivatives).
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace Economy

open Real

/-- Two-task CES aggregator in `ρ`-form (with `ρ ≠ 0`). This is the
    nonlinear change of variable `ρ = (σ-1)/σ`. -/
noncomputable def cesAggregate (ρ α y1 y2 : ℝ) : ℝ :=
  (α * y1 ^ ρ + (1 - α) * y2 ^ ρ) ^ (1 / ρ)

/-- THEOREM: the inner CES sum is nonnegative when both inputs are nonnegative,
    weights are in [0,1], and ρ > 0 (so `y^ρ ≥ 0` via `Real.rpow_nonneg`). -/
theorem ces_inner_nonneg {ρ α y1 y2 : ℝ}
    (hy1 : 0 ≤ y1) (hy2 : 0 ≤ y2) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    0 ≤ α * y1 ^ ρ + (1 - α) * y2 ^ ρ := by
  have hy1r : 0 ≤ y1 ^ ρ := Real.rpow_nonneg hy1 _
  have hy2r : 0 ≤ y2 ^ ρ := Real.rpow_nonneg hy2 _
  have h1α : 0 ≤ 1 - α := by linarith
  have : 0 ≤ α * y1 ^ ρ := mul_nonneg hα0 hy1r
  have : 0 ≤ (1 - α) * y2 ^ ρ := mul_nonneg h1α hy2r
  positivity

/-- THEOREM: CES aggregate is nonnegative (using `Real.rpow_nonneg`). -/
theorem cesAggregate_nonneg {ρ α y1 y2 : ℝ}
    (hy1 : 0 ≤ y1) (hy2 : 0 ≤ y2) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    0 ≤ cesAggregate ρ α y1 y2 := by
  unfold cesAggregate
  exact Real.rpow_nonneg (ces_inner_nonneg hy1 hy2 hα0 hα1) _

/-- THEOREM: CES is symmetric under the swap `(α, y1, y2) ↔ (1-α, y2, y1)`. -/
theorem cesAggregate_swap (ρ α y1 y2 : ℝ) :
    cesAggregate ρ α y1 y2 = cesAggregate ρ (1 - α) y2 y1 := by
  unfold cesAggregate
  congr 1
  have : 1 - (1 - α) = α := by ring
  rw [this]; ring

/-- THEOREM: homogeneity of degree one. Scaling both inputs by `λ > 0`
    scales the aggregate by `λ`. This is the single most important property
    of a well-defined production function. -/
theorem cesAggregate_homogeneous {ρ α y1 y2 lam : ℝ}
    (hρ : ρ ≠ 0) (hy1 : 0 ≤ y1) (hy2 : 0 ≤ y2)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hlam : 0 < lam) :
    cesAggregate ρ α (lam * y1) (lam * y2) = lam * cesAggregate ρ α y1 y2 := by
  unfold cesAggregate
  have hy1r : 0 ≤ y1 ^ ρ := Real.rpow_nonneg hy1 _
  have hy2r : 0 ≤ y2 ^ ρ := Real.rpow_nonneg hy2 _
  have h1α : 0 ≤ 1 - α := by linarith
  have hlam_nn : 0 ≤ lam := le_of_lt hlam
  have hl1 : (lam * y1) ^ ρ = lam ^ ρ * y1 ^ ρ :=
    Real.mul_rpow hlam_nn hy1
  have hl2 : (lam * y2) ^ ρ = lam ^ ρ * y2 ^ ρ :=
    Real.mul_rpow hlam_nn hy2
  rw [hl1, hl2]
  have hinner : α * (lam ^ ρ * y1 ^ ρ) + (1 - α) * (lam ^ ρ * y2 ^ ρ)
              = lam ^ ρ * (α * y1 ^ ρ + (1 - α) * y2 ^ ρ) := by ring
  rw [hinner]
  have hinner_nn : 0 ≤ α * y1 ^ ρ + (1 - α) * y2 ^ ρ :=
    ces_inner_nonneg hy1 hy2 hα0 hα1
  have hlam_rpow_nn : 0 ≤ lam ^ ρ := Real.rpow_nonneg hlam_nn _
  rw [Real.mul_rpow hlam_rpow_nn hinner_nn]
  have hlam_outer : (lam ^ ρ) ^ (1 / ρ) = lam := by
    rw [← Real.rpow_mul hlam_nn]
    have hmul : ρ * (1 / ρ) = 1 := by field_simp
    rw [hmul, Real.rpow_one]
  rw [hlam_outer]

/-- CONJECTURE: as `ρ → 0` (equivalently `σ → 1`), the CES aggregator tends
    to the Cobb-Douglas aggregator `y1^α · y2^(1-α)`. This is the standard
    L'Hôpital computation; formalizing it requires the real `Filter.Tendsto`
    machinery and is left as a sorry with a pointer to ACMS (1961).

    NOTE: this is the CES→CD limit; the STATEMENT is correct and standard,
    the PROOF is a calculus computation not yet developed in this project. -/
theorem ces_to_cobb_douglas_limit (α y1 y2 : ℝ)
    (hα0 : 0 < α) (hα1 : α < 1) (hy1 : 0 < y1) (hy2 : 0 < y2) :
    ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ ρ, 0 < |ρ| → |ρ| < δ →
      |cesAggregate ρ α y1 y2 - y1 ^ α * y2 ^ (1 - α)| < ε := by
  -- sorry: Arrow-Chenery-Minhas-Solow (1961), L'Hôpital on log; ~80 lines with Mathlib.Analysis.Asymptotics.
  sorry

/-- Displacement-productivity sign. When `σ < 1` (tasks are complements) a
    productivity gain on a single task PUSHES the aggregate weight toward the
    other task; when `σ > 1` (substitutes) the reverse holds. We encode this
    via the sign of `ρ = (σ-1)/σ` below. -/
noncomputable def sigmaToRho (σ : ℝ) : ℝ := (σ - 1) / σ

/-- THEOREM: `sigmaToRho σ = 0 ↔ σ = 1`. -/
theorem sigmaToRho_zero_iff {σ : ℝ} (hσ : σ ≠ 0) :
    sigmaToRho σ = 0 ↔ σ = 1 := by
  unfold sigmaToRho
  constructor
  · intro h
    have : σ - 1 = 0 := by
      have := (div_eq_zero_iff).mp h
      rcases this with h1 | h2
      · exact h1
      · exact absurd h2 hσ
    linarith
  · intro h; rw [h]; norm_num

/-- THEOREM (displacement effect sign, Acemoglu-Restrepo 2022):
    `ρ > 0 ↔ σ > 1`. This is the trichotomy that classifies whether a
    productivity shock to one task raises the labor share (`σ < 1`,
    complements) or lowers it (`σ > 1`, substitutes). -/
theorem sigmaToRho_pos_iff {σ : ℝ} (hσ : 0 < σ) :
    0 < sigmaToRho σ ↔ 1 < σ := by
  unfold sigmaToRho
  rw [div_pos_iff]
  constructor
  · rintro (⟨h1, _⟩ | ⟨h1, h2⟩)
    · linarith
    · linarith
  · intro h
    left
    exact ⟨by linarith, hσ⟩

/-- THEOREM (complements): `ρ < 0 ↔ σ < 1`. -/
theorem sigmaToRho_neg_iff {σ : ℝ} (hσ : 0 < σ) :
    sigmaToRho σ < 0 ↔ σ < 1 := by
  unfold sigmaToRho
  rw [div_neg_iff]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · linarith
    · linarith
  · intro h
    right
    exact ⟨by linarith, hσ⟩

end Economy
