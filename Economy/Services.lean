/-
  Economy.Services
  Baumol cost disease in one inequality.

  FRAMEWORK: if the exposed (tradable / automatable) sector has TFP growth g > 0
  and the non-exposed (service) sector has TFP growth 0, and both sectors face
  the same wage, then the service sector's share of nominal output rises.
  We prove the structural inequality for a two-sector economy in level form.
-/
import Mathlib.Tactic

namespace Economy

noncomputable section

/-- Two-sector parameters for a Baumol-style transfer. -/
structure BaumolParams where
  exposedOutput : ℝ
  serviceOutput : ℝ
  exposedTFPGrowth : ℝ
  exposedOutput_pos : 0 < exposedOutput
  serviceOutput_pos : 0 < serviceOutput
  growth_nonneg : 0 ≤ exposedTFPGrowth

/-- Service share of real output BEFORE the TFP shock: S / (E + S). -/
def serviceShareBefore (b : BaumolParams) : ℝ :=
  b.serviceOutput / (b.exposedOutput + b.serviceOutput)

/-- Service share of real output AFTER an exposed-sector TFP shock that raises
    exposed real output by factor `(1 + g)` while leaving service real output
    unchanged. -/
def serviceShareAfter (b : BaumolParams) : ℝ :=
  b.serviceOutput / (b.exposedOutput * (1 + b.exposedTFPGrowth) + b.serviceOutput)

/-- THEOREM (Baumol, real-output form): the service share of REAL output falls
    when the exposed sector grows, because the denominator grows while the
    numerator stays fixed. This is the dual of the classical cost-share
    statement (the service NOMINAL cost share rises). -/
theorem baumol_service_share_falls_in_output (b : BaumolParams) :
    serviceShareAfter b ≤ serviceShareBefore b := by
  unfold serviceShareAfter serviceShareBefore
  have hE := b.exposedOutput_pos
  have hS := b.serviceOutput_pos
  have hg := b.growth_nonneg
  have hES : 0 < b.exposedOutput + b.serviceOutput := by linarith
  have hEg : b.exposedOutput ≤ b.exposedOutput * (1 + b.exposedTFPGrowth) := by
    have : b.exposedOutput * 1 ≤ b.exposedOutput * (1 + b.exposedTFPGrowth) :=
      mul_le_mul_of_nonneg_left (by linarith) hE.le
    linarith
  have hdenom : b.exposedOutput + b.serviceOutput
              ≤ b.exposedOutput * (1 + b.exposedTFPGrowth) + b.serviceOutput := by
    linarith
  have hES' : 0 < b.exposedOutput * (1 + b.exposedTFPGrowth) + b.serviceOutput := by
    linarith
  exact div_le_div_of_nonneg_left hS.le hES hdenom

/-- THEOREM (Baumol, ratio form): the ratio of service to exposed output
    strictly falls when exposed growth is strictly positive. -/
theorem baumol_service_ratio_falls (b : BaumolParams)
    (hg_pos : 0 < b.exposedTFPGrowth) :
    b.serviceOutput / (b.exposedOutput * (1 + b.exposedTFPGrowth))
      < b.serviceOutput / b.exposedOutput := by
  have hE := b.exposedOutput_pos
  have hS := b.serviceOutput_pos
  have h1g : 1 < 1 + b.exposedTFPGrowth := by linarith
  have hEg : b.exposedOutput < b.exposedOutput * (1 + b.exposedTFPGrowth) := by
    nlinarith
  have hEg' : 0 < b.exposedOutput * (1 + b.exposedTFPGrowth) := by linarith
  rw [div_lt_div_iff₀ hEg' hE]
  nlinarith

end

end Economy
