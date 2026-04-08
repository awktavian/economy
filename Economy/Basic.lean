/-
  Economy.Basic
  Core types: Occupation, Task, ExposureShare, Elasticity.

  THEOREM tier: structural facts about the parameter types.
-/
import Mathlib.Tactic

namespace Economy

/-- An occupation identifier (opaque). -/
structure Occupation where
  id : Nat
  deriving DecidableEq, Repr

/-- A task identifier (opaque). -/
structure Task where
  id : Nat
  deriving DecidableEq, Repr

/-- An exposure share lives in the unit interval. A task with exposure `p` has
    a fraction `p` of its labor-content automatable by AI under current capability.

    NUMERICAL OBSERVATION (Brynjolfsson-Chandar-Chen 2025): high-exposure jobs
    for 22-25yo show −6% employment; this is not encoded here — the type only
    records the share, not the employment effect. -/
structure ExposureShare where
  val : ℝ
  nonneg : 0 ≤ val
  le_one : val ≤ 1

namespace ExposureShare

/-- The zero share. -/
def zero : ExposureShare := ⟨0, le_refl 0, by norm_num⟩

/-- The full share. -/
def one : ExposureShare := ⟨1, by norm_num, le_refl 1⟩

end ExposureShare

/-- Elasticity of substitution between AI-automatable and non-automatable tasks.
    FRAMEWORK: Acemoglu w32487 treats this as a free parameter σ > 0. -/
structure Elasticity where
  val : ℝ
  pos : 0 < val

end Economy
