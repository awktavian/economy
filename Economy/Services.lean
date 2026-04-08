/-
  Economy.Services
  Baumol cost disease and Baumol-Bowen growth drag in a two-sector economy.

  ECONOMIC CLAIM: Two sectors — progressive (P, productivity growth g_P > 0) and
  stagnant (S, growth = 0). Results:
  (1) Real output share of S falls as P grows.
  (2) If demand for S is inelastic, nominal employment share of S rises.
  (3) Aggregate growth is bounded above by g_P · (1 - s_S) where s_S is
      stagnant-sector share — the Baumol-Bowen growth drag.

  SOURCES:
  * Baumol (1967), "Macroeconomics of Unbalanced Growth: The Anatomy of Urban
    Crisis", American Economic Review 57(3): 415–426.
  * Baumol & Bowen (1966), "Performing Arts: The Economic Dilemma".
  * Ngai & Pissarides (2007), "Structural Change in a Multisector Model of
    Growth", AER 97(1): 429–443. https://doi.org/10.1257/aer.97.1.429

  TIER: THEOREM for all algebraic results.
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

/-- Service share of real output BEFORE the TFP shock. -/
def serviceShareBefore (b : BaumolParams) : ℝ :=
  b.serviceOutput / (b.exposedOutput + b.serviceOutput)

/-- Service share of real output AFTER the TFP shock (exposed sector grows
    by factor (1 + g)). -/
def serviceShareAfter (b : BaumolParams) : ℝ :=
  b.serviceOutput / (b.exposedOutput * (1 + b.exposedTFPGrowth) + b.serviceOutput)

/-- THEOREM (Baumol real-output dual): service share of REAL output falls
    when the exposed sector grows. -/
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

/-- THEOREM (Baumol ratio form, strict): the ratio S/P strictly falls when
    exposed growth is strictly positive. -/
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

/-- Aggregate real output growth rate (log-linear first order) when the
    exposed-sector share is `sE` and growth is `gP`. -/
def aggregateGrowth (sE gP : ℝ) : ℝ := sE * gP

/-- THEOREM (Baumol-Bowen growth drag): aggregate growth is bounded above by
    `(1 - sS) · gP` where `sS = 1 - sE` is the stagnant-sector share.
    Equivalently: `aggregateGrowth ≤ gP`, with equality iff the stagnant share
    is zero. This is the "drag" — the economy's growth rate is pulled DOWN
    toward the stagnant sector's growth rate (zero). -/
theorem baumol_bowen_drag {sE gP : ℝ} (hsE0 : 0 ≤ sE) (hsE1 : sE ≤ 1)
    (hgP : 0 ≤ gP) :
    aggregateGrowth sE gP ≤ gP := by
  unfold aggregateGrowth
  nlinarith

/-- THEOREM (drag strictness): if the stagnant share is strictly positive and
    the progressive growth rate is strictly positive, the aggregate growth
    rate is strictly below `gP`. -/
theorem baumol_bowen_drag_strict {sE gP : ℝ} (hsE : sE < 1) (hgP : 0 < gP) :
    aggregateGrowth sE gP < gP := by
  unfold aggregateGrowth
  have hs : 0 < 1 - sE := by linarith
  nlinarith

/-- THEOREM (employment share rise, inelastic demand): if the stagnant
    sector's real output stays fixed at `S`, but the nominal outlay on it
    is `pS · S` with `pS` rising to match the wage in the progressive sector
    (wages equalize in a competitive labor market), then `pS · S / (pP · P + pS · S)`
    rises. We formalize the cleanest case: with real outputs P and S fixed
    but the exposed-sector price-level falling by factor (1+g), the NOMINAL
    share of services rises.

    This is the classic "the cost of a live symphony rises faster than the
    cost of a microchip" effect. -/
theorem baumol_nominal_share_rises (b : BaumolParams)
    (hg : 0 < b.exposedTFPGrowth) :
    b.serviceOutput / (b.exposedOutput / (1 + b.exposedTFPGrowth) + b.serviceOutput)
      > b.serviceOutput / (b.exposedOutput + b.serviceOutput) := by
  have hE := b.exposedOutput_pos
  have hS := b.serviceOutput_pos
  have hg1 : 0 < 1 + b.exposedTFPGrowth := by linarith
  have hE_new : b.exposedOutput / (1 + b.exposedTFPGrowth) < b.exposedOutput := by
    rw [div_lt_iff₀ hg1]
    nlinarith
  have hE_new_pos : 0 < b.exposedOutput / (1 + b.exposedTFPGrowth) := by
    exact div_pos hE hg1
  have hden1_pos : 0 < b.exposedOutput / (1 + b.exposedTFPGrowth) + b.serviceOutput := by
    linarith
  have hden2_pos : 0 < b.exposedOutput + b.serviceOutput := by linarith
  rw [gt_iff_lt, div_lt_div_iff₀ hden2_pos hden1_pos]
  nlinarith

end

end Economy
