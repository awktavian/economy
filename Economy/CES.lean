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
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
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

/-- Helper: `f ρ := α · y1^ρ + (1-α) · y2^ρ` has derivative
    `α · log y1 + (1-α) · log y2` at `ρ = 0`, with `f 0 = 1`. -/
private lemma ces_inner_hasDerivAt {α y1 y2 : ℝ}
    (hy1 : 0 < y1) (hy2 : 0 < y2) :
    HasDerivAt (fun ρ : ℝ => α * y1 ^ ρ + (1 - α) * y2 ^ ρ)
      (α * Real.log y1 + (1 - α) * Real.log y2) 0 := by
  have h1 : HasDerivAt (fun ρ : ℝ => y1 ^ ρ) (y1 ^ (0 : ℝ) * Real.log y1) 0 :=
    (hasStrictDerivAt_const_rpow hy1 0).hasDerivAt
  have h2 : HasDerivAt (fun ρ : ℝ => y2 ^ ρ) (y2 ^ (0 : ℝ) * Real.log y2) 0 :=
    (hasStrictDerivAt_const_rpow hy2 0).hasDerivAt
  have h1' : HasDerivAt (fun ρ : ℝ => y1 ^ ρ) (Real.log y1) 0 := by
    simpa [Real.rpow_zero] using h1
  have h2' : HasDerivAt (fun ρ : ℝ => y2 ^ ρ) (Real.log y2) 0 := by
    simpa [Real.rpow_zero] using h2
  exact (h1'.const_mul α).add (h2'.const_mul (1 - α))

/-- THEOREM (Arrow-Chenery-Minhas-Solow 1961): as `ρ → 0`, the CES aggregator
    tends to the Cobb-Douglas aggregator `y1^α · y2^(1-α)`.

    Proof: `cesAggregate ρ = f(ρ)^(1/ρ) = exp(log(f(ρ))/ρ)` where
    `f(ρ) = α·y1^ρ + (1-α)·y2^ρ`. Since `f(0) = 1` and `f'(0) = α·log y1 +
    (1-α)·log y2`, the logarithmic difference quotient `log(f(ρ))/ρ` tends
    to `f'(0)`, and exponentiating gives `exp(α·log y1 + (1-α)·log y2) =
    y1^α · y2^(1-α)`. -/
theorem ces_to_cobb_douglas_limit (α y1 y2 : ℝ)
    (hα0 : 0 < α) (hα1 : α < 1) (hy1 : 0 < y1) (hy2 : 0 < y2) :
    ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ ρ, 0 < |ρ| → |ρ| < δ →
      |cesAggregate ρ α y1 y2 - y1 ^ α * y2 ^ (1 - α)| < ε := by
  -- Set up the limit L := α·log y1 + (1-α)·log y2 and target = exp L = y1^α·y2^(1-α).
  set L : ℝ := α * Real.log y1 + (1 - α) * Real.log y2 with hLdef
  have hα0' : 0 ≤ α := le_of_lt hα0
  have h1α : 0 ≤ 1 - α := by linarith
  -- f ρ := α·y1^ρ + (1-α)·y2^ρ, with f 0 = 1 and f'(0) = L.
  set f : ℝ → ℝ := fun ρ => α * y1 ^ ρ + (1 - α) * y2 ^ ρ with hfdef
  have hf0 : f 0 = 1 := by
    simp [f, Real.rpow_zero]
  have hfderiv : HasDerivAt f L 0 := ces_inner_hasDerivAt hy1 hy2
  -- g ρ := log (f ρ). Since f 0 = 1 > 0, g is differentiable at 0 with g'(0) = L/1 = L.
  have hf0pos : (0 : ℝ) < f 0 := by rw [hf0]; exact one_pos
  have hgderiv : HasDerivAt (fun ρ => Real.log (f ρ)) (L / f 0) 0 :=
    hfderiv.log (ne_of_gt hf0pos)
  have hgderiv' : HasDerivAt (fun ρ => Real.log (f ρ)) L 0 := by
    have : L / f 0 = L := by rw [hf0]; ring
    rw [this] at hgderiv; exact hgderiv
  -- At ρ=0, log(f 0) = log 1 = 0.
  have hg0 : Real.log (f 0) = 0 := by rw [hf0]; exact Real.log_one
  -- The difference quotient (log(f ρ) - log(f 0))/(ρ - 0) = log(f ρ)/ρ tends to L.
  have hquot : Filter.Tendsto (fun ρ : ℝ => Real.log (f ρ) / ρ)
      (nhdsWithin 0 {0}ᶜ) (nhds L) := by
    have hs := hgderiv'.tendsto_slope
    refine hs.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ρ hρ
    simp only [slope, vsub_eq_sub, smul_eq_mul, hg0, sub_zero]
    rw [div_eq_inv_mul]
  -- exp ∘ (log(f ρ)/ρ) → exp L = y1^α · y2^(1-α)
  have hexp : Filter.Tendsto (fun ρ : ℝ => Real.exp (Real.log (f ρ) / ρ))
      (nhdsWithin 0 {0}ᶜ) (nhds (Real.exp L)) :=
    (Real.continuous_exp.tendsto L).comp hquot
  -- exp L = y1^α * y2^(1-α)
  have hexpL : Real.exp L = y1 ^ α * y2 ^ (1 - α) := by
    show Real.exp (α * Real.log y1 + (1 - α) * Real.log y2) = y1 ^ α * y2 ^ (1 - α)
    rw [Real.exp_add, mul_comm α (Real.log y1), mul_comm (1 - α) (Real.log y2),
        ← Real.rpow_def_of_pos hy1, ← Real.rpow_def_of_pos hy2]
  -- For ρ ≠ 0 with f ρ > 0: cesAggregate ρ α y1 y2 = exp(log(f ρ)/ρ).
  have hces_eq : ∀ ρ : ℝ, 0 < f ρ → ρ ≠ 0 →
      cesAggregate ρ α y1 y2 = Real.exp (Real.log (f ρ) / ρ) := by
    intro ρ hfρ hρ
    unfold cesAggregate
    show (f ρ) ^ (1 / ρ) = Real.exp (Real.log (f ρ) / ρ)
    rw [Real.rpow_def_of_pos hfρ]
    ring_nf
  -- f ρ > 0 for all ρ (since y1, y2 > 0 and α ∈ (0,1))
  have hfpos : ∀ ρ : ℝ, 0 < f ρ := by
    intro ρ
    have h1 : 0 < y1 ^ ρ := Real.rpow_pos_of_pos hy1 _
    have h2 : 0 < y2 ^ ρ := Real.rpow_pos_of_pos hy2 _
    have hαy1 : 0 < α * y1 ^ ρ := mul_pos hα0 h1
    have h1αy2 : 0 < (1 - α) * y2 ^ ρ := mul_pos (by linarith) h2
    show 0 < α * y1 ^ ρ + (1 - α) * y2 ^ ρ
    linarith
  -- Now the ε-δ game.
  intro ε hε
  have hexp' := hexp
  rw [hexpL] at hexp'
  rw [Metric.tendsto_nhdsWithin_nhds] at hexp'
  obtain ⟨δ, hδpos, hδ⟩ := hexp' ε hε
  refine ⟨δ, hδpos, ?_⟩
  intro ρ hρabs hρδ
  have hρne : ρ ≠ 0 := by
    intro h; rw [h, abs_zero] at hρabs; exact lt_irrefl 0 hρabs
  have hρmem : ρ ∈ ({0}ᶜ : Set ℝ) := by
    simp [hρne]
  have hdist : dist ρ 0 < δ := by rw [Real.dist_eq, sub_zero]; exact hρδ
  have hfinal := hδ hρmem hdist
  rw [Real.dist_eq] at hfinal
  have heq := hces_eq ρ (hfpos ρ) hρne
  rw [heq]
  exact hfinal

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
