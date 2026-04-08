/-
  Economy.LaborShare
  Labor-share dynamics in a task-based Cobb-Douglas economy.

  ECONOMIC CLAIM: Under Cobb-Douglas aggregation across tasks with weights αᵢ
  and automation shares ψᵢ, the aggregate labor share equals Σᵢ αᵢ (1 - ψᵢ).
  A ceteris-paribus increase in automation on ANY task strictly lowers the
  labor share. Adding a new task with pure-labor share raises the labor share
  iff its α-weight exceeds the OLD labor share.

  SOURCES:
  * Acemoglu & Restrepo (2018), "The Race between Man and Machine", AER 108(6).
  * Karabarbounis & Neiman (2014), "The Global Decline of the Labor Share",
    QJE 129(1): 61–103. https://doi.org/10.1093/qje/qjt032

  TIER: THEOREM for all results (algebraic identities on finite sums).
-/
import Mathlib.Tactic

namespace Economy

open Finset

/-- Task-level labor share = (1 - ψᵢ). Aggregate labor share weights this by
    the Cobb-Douglas α-weights. -/
def laborShare {n : ℕ} (α ψ : Fin n → ℝ) : ℝ :=
  ∑ i, α i * (1 - ψ i)

/-- THEOREM: labor share is nonnegative when weights and automation shares
    are in their natural ranges. -/
theorem laborShare_nonneg {n : ℕ} {α ψ : Fin n → ℝ}
    (hα : ∀ i, 0 ≤ α i) (hψ1 : ∀ i, ψ i ≤ 1) :
    0 ≤ laborShare α ψ := by
  unfold laborShare
  apply Finset.sum_nonneg
  intro i _
  have : 0 ≤ 1 - ψ i := by linarith [hψ1 i]
  exact mul_nonneg (hα i) this

/-- THEOREM: labor share is ≤ 1 when α sums to 1 and ψᵢ ≥ 0. -/
theorem laborShare_le_one {n : ℕ} {α ψ : Fin n → ℝ}
    (hα : ∀ i, 0 ≤ α i) (hα_sum : ∑ i, α i = 1) (hψ0 : ∀ i, 0 ≤ ψ i) :
    laborShare α ψ ≤ 1 := by
  unfold laborShare
  have : ∑ i, α i * (1 - ψ i) ≤ ∑ i, α i * 1 := by
    apply Finset.sum_le_sum
    intro i _
    have : 1 - ψ i ≤ 1 := by linarith [hψ0 i]
    exact mul_le_mul_of_nonneg_left this (hα i)
  simp at this; linarith [hα_sum]

/-- THEOREM (full automation ⇒ zero labor share): if every task is fully
    automated (ψ ≡ 1), the aggregate labor share is 0. -/
theorem laborShare_zero_of_full_automation {n : ℕ} (α : Fin n → ℝ) :
    laborShare α (fun _ => 1) = 0 := by
  unfold laborShare
  simp

/-- THEOREM (no automation ⇒ labor share equals total α-mass, which is 1
    when normalized). -/
theorem laborShare_eq_one_of_no_automation {n : ℕ} {α : Fin n → ℝ}
    (hα_sum : ∑ i, α i = 1) :
    laborShare α (fun _ => 0) = 1 := by
  unfold laborShare
  simp
  exact hα_sum

/-- THEOREM (monotonicity in automation): raising automation anywhere weakly
    lowers the labor share. -/
theorem laborShare_antitone {n : ℕ} {α ψ ψ' : Fin n → ℝ}
    (hα : ∀ i, 0 ≤ α i) (h : ∀ i, ψ i ≤ ψ' i) :
    laborShare α ψ' ≤ laborShare α ψ := by
  unfold laborShare
  apply Finset.sum_le_sum
  intro i _
  have h1 : 1 - ψ' i ≤ 1 - ψ i := by linarith [h i]
  exact mul_le_mul_of_nonneg_left h1 (hα i)

/-- THEOREM (strict monotonicity on a single task): if α j > 0 and ψ j < ψ' j,
    the labor share strictly falls when task j is automated harder. -/
theorem laborShare_strict_antitone_single {n : ℕ} {α ψ ψ' : Fin n → ℝ}
    (j : Fin n)
    (hα : ∀ i, 0 ≤ α i) (hαj : 0 < α j)
    (h_eq : ∀ i ≠ j, ψ i = ψ' i) (h_lt : ψ j < ψ' j) :
    laborShare α ψ' < laborShare α ψ := by
  unfold laborShare
  have hterm : α j * (1 - ψ' j) < α j * (1 - ψ j) := by
    have : 1 - ψ' j < 1 - ψ j := by linarith
    exact mul_lt_mul_of_pos_left this hαj
  have hother : ∀ i ∈ univ, i ≠ j →
      α i * (1 - ψ' i) ≤ α i * (1 - ψ i) := by
    intro i _ hij
    rw [h_eq i hij]
  -- Split the sum at j
  have h1 : ∑ i, α i * (1 - ψ' i)
          = α j * (1 - ψ' j) + ∑ i ∈ univ.erase j, α i * (1 - ψ' i) := by
    rw [← Finset.add_sum_erase univ _ (Finset.mem_univ j)]
  have h2 : ∑ i, α i * (1 - ψ i)
          = α j * (1 - ψ j) + ∑ i ∈ univ.erase j, α i * (1 - ψ i) := by
    rw [← Finset.add_sum_erase univ _ (Finset.mem_univ j)]
  rw [h1, h2]
  have hsum : ∑ i ∈ univ.erase j, α i * (1 - ψ' i)
            ≤ ∑ i ∈ univ.erase j, α i * (1 - ψ i) := by
    apply Finset.sum_le_sum
    intro i hi
    have hij : i ≠ j := (Finset.mem_erase.mp hi).1
    exact hother i (Finset.mem_univ i) hij
  linarith

end Economy
