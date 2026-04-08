/-
  Economy.Welfare
  Welfare bounds for a representative-consumer log utility.

  ECONOMIC CLAIM: With log utility U = log C, welfare change equals log C' - log C.
  Under Cobb-Douglas task aggregation with competitive pricing, log C equals
  log Y minus a labor-leisure term. The key observation (Acemoglu-Restrepo 2022)
  is that welfare can FALL even when GDP rises: if labor share collapses faster
  than productivity rises, the representative worker's consumption share shrinks.

  SOURCES:
  * Acemoglu & Restrepo (2022), "Tasks, Automation, and the Rise in U.S. Wage
    Inequality", Econometrica 90(5): 1973–2016.
  * Acemoglu (2024), "The Simple Macroeconomics of AI", NBER w32487, §5.

  TIER: THEOREM for monotonicity under log; CONJECTURE (sorry) for the
  Jensen-on-CES welfare-GDP gap (needs the CES→CD limit and concavity machinery).
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Economy

open Real

/-- Log-utility welfare change, given baseline consumption C and new C'. -/
noncomputable def welfareDelta (C C' : ℝ) : ℝ := Real.log C' - Real.log C

/-- THEOREM (sign): welfare rises iff consumption rises (both positive). -/
theorem welfareDelta_pos_iff {C C' : ℝ} (hC : 0 < C) (hC' : 0 < C') :
    0 < welfareDelta C C' ↔ C < C' := by
  unfold welfareDelta
  constructor
  · intro h
    have := Real.log_lt_log_iff hC hC' |>.mp (by linarith)
    exact this
  · intro h
    have : Real.log C < Real.log C' := (Real.log_lt_log_iff hC hC').mpr h
    linarith

/-- THEOREM (welfare falls iff consumption falls). -/
theorem welfareDelta_neg_iff {C C' : ℝ} (hC : 0 < C) (hC' : 0 < C') :
    welfareDelta C C' < 0 ↔ C' < C := by
  unfold welfareDelta
  constructor
  · intro h
    exact (Real.log_lt_log_iff hC' hC).mp (by linarith)
  · intro h
    have : Real.log C' < Real.log C := (Real.log_lt_log_iff hC' hC).mpr h
    linarith

/-- THEOREM (GDP-welfare gap): if consumption is a fraction `λ ∈ (0,1]` of
    output, and output grows from Y to Y' while the labor share drops from
    λ to λ', welfare change equals log(λ'/λ) + log(Y'/Y). If the first term
    is sufficiently negative, welfare falls even when Y' > Y.

    This is the formal statement of the Acemoglu-Restrepo welfare-GDP gap:
    productivity gains and welfare gains can diverge. -/
theorem welfare_gdp_gap {Y Y' lam lam' : ℝ}
    (hY : 0 < Y) (hY' : 0 < Y') (hlam : 0 < lam) (hlamp : 0 < lam') :
    welfareDelta (lam * Y) (lam' * Y') =
      (Real.log lam' - Real.log lam) + (Real.log Y' - Real.log Y) := by
  unfold welfareDelta
  have h1 : Real.log (lam' * Y') = Real.log lam' + Real.log Y' :=
    Real.log_mul (ne_of_gt hlamp) (ne_of_gt hY')
  have h2 : Real.log (lam * Y) = Real.log lam + Real.log Y :=
    Real.log_mul (ne_of_gt hlam) (ne_of_gt hY)
  rw [h1, h2]; ring

/-- THEOREM (welfare can fall when GDP rises): explicit witness. If the
    labor share falls by a factor `λ'/λ = 1/2` and GDP rises by `Y'/Y = 1.1`,
    welfare falls because `log(1.1) + log(1/2) = log(0.55) < 0`. -/
theorem welfare_can_fall_with_gdp_rise :
    ∃ (Y Y' lam lam' : ℝ), 0 < Y ∧ 0 < Y' ∧ 0 < lam ∧ 0 < lam'
      ∧ Y < Y' ∧ welfareDelta (lam * Y) (lam' * Y') < 0 := by
  refine ⟨1, (11 : ℝ) / 10, 1, (1 : ℝ) / 2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · -- welfareDelta (1 * 1) (1/2 * 11/10) = log(11/20) - log(1) = log(11/20) < 0
    unfold welfareDelta
    have h1 : (1 : ℝ) * 1 = 1 := by ring
    have h2 : ((1 : ℝ) / 2) * (11 / 10) = 11 / 20 := by ring
    rw [h1, h2, Real.log_one]
    have : (11 : ℝ) / 20 < 1 := by norm_num
    have hpos : (0 : ℝ) < 11 / 20 := by norm_num
    have := Real.log_neg hpos this
    linarith

/-- THEOREM (welfare additivity): welfare changes compose additively. -/
theorem welfareDelta_trans (C1 C2 C3 : ℝ) :
    welfareDelta C1 C2 + welfareDelta C2 C3 = welfareDelta C1 C3 := by
  unfold welfareDelta; ring

end Economy
