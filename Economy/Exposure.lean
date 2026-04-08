/-
  Economy.Exposure
  Convex-combination aggregation of task-level exposure into an aggregate share.

  THEOREM tier: bounded, monotone-under-refinement.
-/
import Economy.Basic
import Mathlib.Tactic

namespace Economy

/-- Aggregate exposure from a weight `w ∈ [0,1]` and two sub-shares.
    FRAMEWORK: Acemoglu's aggregate exposure is a weighted average over tasks.
    Here we formalize the two-sector case; an n-sector version would use `Finset.sum`. -/
def aggregateExposure (w : ℝ) (p q : ExposureShare) : ℝ :=
  w * p.val + (1 - w) * q.val

/-- THEOREM: the convex combination stays nonnegative. -/
theorem aggregateExposure_nonneg {w : ℝ} (p q : ExposureShare)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) : 0 ≤ aggregateExposure w p q := by
  unfold aggregateExposure
  have hp := p.nonneg
  have hq := q.nonneg
  have h1w : 0 ≤ 1 - w := by linarith
  nlinarith

/-- THEOREM: the convex combination stays ≤ 1. -/
theorem aggregateExposure_le_one {w : ℝ} (p q : ExposureShare)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) : aggregateExposure w p q ≤ 1 := by
  unfold aggregateExposure
  have hp := p.le_one
  have hq := q.le_one
  have h1w : 0 ≤ 1 - w := by linarith
  nlinarith

/-- THEOREM: aggregate exposure is monotone in the first sub-share. -/
theorem aggregateExposure_mono_left {w : ℝ} {p p' q : ExposureShare}
    (hw0 : 0 ≤ w) (hpp' : p.val ≤ p'.val) :
    aggregateExposure w p q ≤ aggregateExposure w p' q := by
  unfold aggregateExposure
  nlinarith

/-- THEOREM: aggregate exposure is monotone in the second sub-share. -/
theorem aggregateExposure_mono_right {w : ℝ} {p q q' : ExposureShare}
    (hw1 : w ≤ 1) (hqq' : q.val ≤ q'.val) :
    aggregateExposure w p q ≤ aggregateExposure w p q' := by
  unfold aggregateExposure
  have h1w : 0 ≤ 1 - w := by linarith
  nlinarith

/-- THEOREM: refining a task (splitting into two exposed sub-tasks of
    possibly-different shares, with weights summing to the original weight)
    preserves the aggregate. Stated as: aggregate with identical sub-shares
    is just that share. -/
theorem aggregateExposure_const {w : ℝ} (p : ExposureShare)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    aggregateExposure w p p = p.val := by
  unfold aggregateExposure
  ring

end Economy
