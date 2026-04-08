/-
  Economy.TaskModel
  Task-based production with Cobb-Douglas aggregation.

  ECONOMIC CLAIM: Output Y is a Cobb-Douglas aggregate of n task-level
  outputs y_i, where y_i = A_i · (ψ_i · k_i + (1-ψ_i) · ℓ_i). The Cobb-Douglas
  weights αᵢ sum to 1. log Y = Σ αᵢ log y_i. Newly automated tasks contribute
  to aggregate TFP via Hulten's theorem: ΔlogY ≈ Σ αᵢ Δlog A_i.

  SOURCES:
  * Zeira (1998), "Workers, Machines, and Economic Growth", QJE 113(4): 1091–1117.
    https://doi.org/10.1162/003355398555847
  * Acemoglu & Restrepo (2018), "The Race between Man and Machine:
    Implications of Technology for Growth, Factor Shares, and Employment",
    AER 108(6): 1488–1542. https://doi.org/10.1257/aer.20160696
  * Acemoglu (2024), "The Simple Macroeconomics of AI", NBER w32487.
    https://www.nber.org/papers/w32487
  * Hulten (1978), "Growth Accounting with Intermediate Inputs",
    Review of Economic Studies 45(3): 511–518.

  TIER: THEOREM for algebraic identities (log-decomposition, weight sum,
  exposure share bounds); CONJECTURE for the differentiable-envelope form
  of Hulten (stated with sorry + citation to Hulten 1978).
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Economy

open Finset Real

/-- A task economy: `n` tasks, each with a productivity `A i > 0`, an
    automation share `ψ i ∈ [0,1]`, a capital stock `k i ≥ 0`, a labor input
    `ℓ i ≥ 0`, and a Cobb-Douglas weight `α i ≥ 0`. The weights sum to 1. -/
structure TaskEconomy (n : ℕ) where
  A : Fin n → ℝ
  ψ : Fin n → ℝ
  k : Fin n → ℝ
  ℓ : Fin n → ℝ
  α : Fin n → ℝ
  A_pos : ∀ i, 0 < A i
  psi_nonneg : ∀ i, 0 ≤ ψ i
  psi_le_one : ∀ i, ψ i ≤ 1
  k_nonneg : ∀ i, 0 ≤ k i
  l_nonneg : ∀ i, 0 ≤ ℓ i
  alpha_nonneg : ∀ i, 0 ≤ α i
  alpha_sum_one : ∑ i, α i = 1
  /-- Positivity of factor input on every task, so `log y i` is well defined. -/
  input_pos : ∀ i, 0 < ψ i * k i + (1 - ψ i) * ℓ i

namespace TaskEconomy

variable {n : ℕ} (E : TaskEconomy n)

/-- Task-level output: `y_i = A_i · (ψ_i k_i + (1 - ψ_i) ℓ_i)`. -/
def y (i : Fin n) : ℝ := E.A i * (E.ψ i * E.k i + (1 - E.ψ i) * E.ℓ i)

/-- Positivity of task output. -/
theorem y_pos (i : Fin n) : 0 < E.y i := by
  unfold y
  exact mul_pos (E.A_pos i) (E.input_pos i)

/-- Aggregate Cobb-Douglas output: `Y = ∏ᵢ (y i)^(α i)`. -/
noncomputable def Y : ℝ := ∏ i, (E.y i) ^ (E.α i)

/-- THEOREM (log-linearity of Cobb-Douglas):
    `log Y = Σ αᵢ log (y i)`. This is the algebraic core from which Hulten's
    marginal-product identity follows; it is proved from `Real.log_prod` and
    `Real.log_rpow`. -/
theorem log_Y_eq : Real.log (E.Y) = ∑ i, E.α i * Real.log (E.y i) := by
  unfold Y
  rw [Real.log_prod]
  · apply Finset.sum_congr rfl
    intro i _
    rw [Real.log_rpow (E.y_pos i)]
  · intro i _
    exact (Real.rpow_pos_of_pos (E.y_pos i) _).ne'

/-- The *exposure share* of a subset `S ⊆ Fin n` of tasks: the sum of their
    Cobb-Douglas weights. In the task model, the exposure share is the
    "α-mass" of tasks that are now automatable. -/
def exposureShare (S : Finset (Fin n)) : ℝ := ∑ i ∈ S, E.α i

/-- THEOREM: exposure share is in [0,1]. -/
theorem exposureShare_mem_unit (S : Finset (Fin n)) :
    0 ≤ E.exposureShare S ∧ E.exposureShare S ≤ 1 := by
  refine ⟨?_, ?_⟩
  · exact Finset.sum_nonneg (fun i _ => E.alpha_nonneg i)
  · unfold exposureShare
    have h := E.alpha_sum_one
    have : ∑ i ∈ S, E.α i ≤ ∑ i, E.α i :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
        (fun i _ _ => E.alpha_nonneg i)
    linarith

/-- THEOREM: exposure share is monotone in the task set (adding a task
    can only raise the share). -/
theorem exposureShare_mono {S T : Finset (Fin n)} (h : S ⊆ T) :
    E.exposureShare S ≤ E.exposureShare T := by
  unfold exposureShare
  exact Finset.sum_le_sum_of_subset_of_nonneg h
    (fun i _ _ => E.alpha_nonneg i)

/-- THEOREM (Hulten decomposition, discrete form):
    If productivities change from `A` to `A'` while `ψ, k, ℓ` stay fixed, then
    `log Y' - log Y = Σ αᵢ (log A'_i - log A_i)`.

    This is the DISCRETE version of Hulten's theorem (the differentiable version
    requires calculus machinery we don't develop here; that's stated as a separate
    conjecture below). The discrete version is the one actually used in growth
    accounting. -/
theorem hulten_discrete (E' : TaskEconomy n)
    (hψ : E'.ψ = E.ψ) (hk : E'.k = E.k) (hℓ : E'.ℓ = E.ℓ)
    (hα : E'.α = E.α) :
    Real.log (E'.Y) - Real.log (E.Y) =
      ∑ i, E.α i * (Real.log (E'.A i) - Real.log (E.A i)) := by
  rw [E.log_Y_eq, E'.log_Y_eq, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hyi : E'.y i = (E'.A i / E.A i) * E.y i := by
    unfold y
    rw [show E'.ψ i = E.ψ i from by rw [hψ],
        show E'.k i = E.k i from by rw [hk],
        show E'.ℓ i = E.ℓ i from by rw [hℓ]]
    have hA : E.A i ≠ 0 := ne_of_gt (E.A_pos i)
    field_simp
  have hA' : 0 < E'.A i := E'.A_pos i
  have hA  : 0 < E.A i := E.A_pos i
  have hyipos : 0 < E'.y i := E'.y_pos i
  have hyiE  : 0 < E.y i := E.y_pos i
  have : Real.log (E'.y i) - Real.log (E.y i)
        = Real.log (E'.A i) - Real.log (E.A i) := by
    have h1 : Real.log (E'.y i) = Real.log (E'.A i / E.A i) + Real.log (E.y i) := by
      rw [hyi, Real.log_mul (by positivity) (ne_of_gt hyiE)]
    rw [h1, Real.log_div (ne_of_gt hA') (ne_of_gt hA)]
    ring
  rw [hα]
  have heq : E.α i * Real.log (E'.y i) - E.α i * Real.log (E.y i)
           = E.α i * (Real.log (E'.y i) - Real.log (E.y i)) := by ring
  rw [heq, this]

/-- THEOREM (Acemoglu macro bound, discrete corollary of Hulten):
    If productivity changes only on a set `S` of newly automated tasks, and
    each such task sees `log A'_i - log A_i ≤ c` for a common `c ≥ 0`, then
    the aggregate log-TFP change is at most `exposureShare(S) · c`.
    This is the bound Acemoglu (w32487) states in the abstract. -/
theorem acemoglu_macro_bound (E' : TaskEconomy n) (S : Finset (Fin n)) (c : ℝ)
    (hc : 0 ≤ c)
    (hψ : E'.ψ = E.ψ) (hk : E'.k = E.k) (hℓ : E'.ℓ = E.ℓ) (hα : E'.α = E.α)
    (h_untouched : ∀ i ∉ S, E'.A i = E.A i)
    (h_bounded : ∀ i ∈ S, Real.log (E'.A i) - Real.log (E.A i) ≤ c) :
    Real.log (E'.Y) - Real.log (E.Y) ≤ E.exposureShare S * c := by
  rw [E.hulten_discrete E' hψ hk hℓ hα]
  have hsplit :
      ∑ i, E.α i * (Real.log (E'.A i) - Real.log (E.A i))
        = ∑ i ∈ S, E.α i * (Real.log (E'.A i) - Real.log (E.A i)) := by
    rw [← Finset.sum_filter_add_sum_filter_not univ (· ∈ S)]
    have h_out : ∑ i ∈ univ.filter (¬ · ∈ S),
        E.α i * (Real.log (E'.A i) - Real.log (E.A i)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp at hi
      rw [h_untouched i hi]; ring
    rw [h_out, add_zero]
    apply Finset.sum_congr ?_ (fun _ _ => rfl)
    ext i; simp
  rw [hsplit]
  have hbnd : ∀ i ∈ S,
      E.α i * (Real.log (E'.A i) - Real.log (E.A i)) ≤ E.α i * c := by
    intro i hi
    exact mul_le_mul_of_nonneg_left (h_bounded i hi) (E.alpha_nonneg i)
  calc ∑ i ∈ S, E.α i * (Real.log (E'.A i) - Real.log (E.A i))
      ≤ ∑ i ∈ S, E.α i * c := Finset.sum_le_sum hbnd
    _ = (∑ i ∈ S, E.α i) * c := by rw [← Finset.sum_mul]
    _ = E.exposureShare S * c := rfl

end TaskEconomy

end Economy
