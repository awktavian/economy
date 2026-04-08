/-
  Economy.LaborMarket
  Two-sector reinstatement vs displacement accounting.

  FRAMEWORK: Acemoglu-Restrepo task-based labor accounting. Employment change
  equals reinstatement (new tasks created, productivity effect) minus
  displacement (tasks automated away).

  NUMERICAL OBSERVATION: Brynjolfsson-Chandar-Chen (Stanford, 2025) measure
  −6% employment for 22-25yo in high-exposure occupations late 2022–Jul 2025.
  That empirical number is NOT derived here; this file only proves that the
  sign of `employmentDelta` matches the sign of `reinstatement − displacement`.
-/
import Mathlib.Tactic

namespace Economy

/-- Labor-market flow parameters for a single occupation / cohort. -/
structure LaborParams where
  reinstatement : ℝ  -- new tasks / productivity-driven rehiring (≥ 0)
  displacement : ℝ   -- tasks automated away (≥ 0)
  rein_nonneg : 0 ≤ reinstatement
  disp_nonneg : 0 ≤ displacement

/-- Net employment change. -/
def employmentDelta (p : LaborParams) : ℝ :=
  p.reinstatement - p.displacement

/-- THEOREM: employment declines iff reinstatement is strictly less than displacement. -/
theorem employment_decline_iff (p : LaborParams) :
    employmentDelta p < 0 ↔ p.reinstatement < p.displacement := by
  unfold employmentDelta
  constructor
  · intro h; linarith
  · intro h; linarith

/-- THEOREM: employment grows iff reinstatement strictly exceeds displacement. -/
theorem employment_grow_iff (p : LaborParams) :
    0 < employmentDelta p ↔ p.displacement < p.reinstatement := by
  unfold employmentDelta
  constructor
  · intro h; linarith
  · intro h; linarith

/-- THEOREM: employment is monotone in reinstatement. -/
theorem employmentDelta_mono_rein {p q : LaborParams}
    (h_disp : p.displacement = q.displacement)
    (h_rein : p.reinstatement ≤ q.reinstatement) :
    employmentDelta p ≤ employmentDelta q := by
  unfold employmentDelta
  rw [h_disp]; linarith

/-- THEOREM: employment is antitone in displacement. -/
theorem employmentDelta_antitone_disp {p q : LaborParams}
    (h_rein : p.reinstatement = q.reinstatement)
    (h_disp : p.displacement ≤ q.displacement) :
    employmentDelta q ≤ employmentDelta p := by
  unfold employmentDelta
  rw [h_rein]; linarith

end Economy
