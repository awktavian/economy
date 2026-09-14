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
theorem baumol_bowen_drag {sE gP : ℝ} (hsE1 : sE ≤ 1) (hgP : 0 ≤ gP) :
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


/-! ### Carrier consumption — shares as genuine shares, strictness, drag at the carrier -/

/-- THEOREM (share well-posedness): the pre-shock service share is a genuine
    share, strictly between 0 and 1. The lower bound uses `serviceOutput_pos`
    and the upper bound `exposedOutput_pos` — neither holds for an arbitrary
    pair of reals, so these carry the carrier's economic content. -/
theorem serviceShareBefore_pos (b : BaumolParams) : 0 < serviceShareBefore b := by
  have hE := b.exposedOutput_pos
  have hS := b.serviceOutput_pos
  unfold serviceShareBefore
  exact div_pos hS (by linarith)

theorem serviceShareBefore_lt_one (b : BaumolParams) : serviceShareBefore b < 1 := by
  have hE := b.exposedOutput_pos
  have hS := b.serviceOutput_pos
  unfold serviceShareBefore
  rw [div_lt_one (by linarith)]
  linarith

/-- THEOREM: the post-shock service share is likewise a genuine share. -/
theorem serviceShareAfter_pos (b : BaumolParams) : 0 < serviceShareAfter b := by
  have hE := b.exposedOutput_pos
  have hS := b.serviceOutput_pos
  have hg := b.growth_nonneg
  unfold serviceShareAfter
  have h1g : 0 < 1 + b.exposedTFPGrowth := by linarith
  exact div_pos hS (by nlinarith)

theorem serviceShareAfter_lt_one (b : BaumolParams) : serviceShareAfter b < 1 := by
  have hE := b.exposedOutput_pos
  have hS := b.serviceOutput_pos
  have hg := b.growth_nonneg
  unfold serviceShareAfter
  have hEg : 0 < b.exposedOutput * (1 + b.exposedTFPGrowth) := by nlinarith
  rw [div_lt_one (by nlinarith)]
  nlinarith

/-- THEOREM (strict real-output dual): with STRICTLY positive exposed growth
    the service share falls strictly. The carrier only assumes `0 <= g`, and at
    `g = 0` the shares coincide (`serviceShareAfter_eq_of_growth_zero`), so the
    side condition is exactly the content boundary of the strict statement. -/
theorem baumol_service_share_falls_strict (b : BaumolParams)
    (hg : 0 < b.exposedTFPGrowth) :
    serviceShareAfter b < serviceShareBefore b := by
  have hE := b.exposedOutput_pos
  have hS := b.serviceOutput_pos
  unfold serviceShareAfter serviceShareBefore
  have hden1 : 0 < b.exposedOutput * (1 + b.exposedTFPGrowth) + b.serviceOutput := by
    nlinarith
  rw [div_lt_div_iff₀ hden1 (by linarith)]
  have hSE : 0 < b.serviceOutput * b.exposedOutput := mul_pos hS hE
  have hSEg : 0 < b.serviceOutput * b.exposedOutput * b.exposedTFPGrowth :=
    mul_pos hSE hg
  nlinarith

/-- THEOREM (boundary of strictness): at zero exposed growth the share does
    not move, so `0 < g` in `baumol_service_share_falls_strict` is tight. -/
theorem serviceShareAfter_eq_of_growth_zero (b : BaumolParams)
    (hg : b.exposedTFPGrowth = 0) : serviceShareAfter b = serviceShareBefore b := by
  unfold serviceShareAfter serviceShareBefore
  rw [hg]
  ring

/-- THEOREM (Baumol-Bowen drag at the carrier): taking the progressive-sector
    share to be the exposed output share `1 - serviceShareBefore b`, aggregate
    growth is bounded by — and since every carrier instance has a STRICTLY
    positive service share, always strictly below — progressive growth. This is
    the permanent-drag statement: it consumes `serviceShareBefore` and
    `aggregateGrowth` together. -/
theorem baumol_drag_serviceShare {b : BaumolParams} {gP : ℝ} (hgP : 0 ≤ gP) :
    aggregateGrowth (1 - serviceShareBefore b) gP ≤ gP :=
  baumol_bowen_drag (by linarith [serviceShareBefore_pos b]) hgP

theorem baumol_drag_serviceShare_strict {b : BaumolParams} {gP : ℝ} (hgP : 0 < gP) :
    aggregateGrowth (1 - serviceShareBefore b) gP < gP :=
  baumol_bowen_drag_strict (by linarith [serviceShareBefore_pos b]) hgP

end

end Economy
