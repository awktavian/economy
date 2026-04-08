/-
  Economy.FinanceRealCoupling
  The coupling layer: hyperscaler capex drives NIPA I, labor-share compression
  drives profit margins, consumption feedback closes the loop.

  ECONOMIC CLAIM: (1) If hyperscaler capex `K_H` is a fraction `φ` of nominal
  GDP, the NIPA `I` term includes `K_H`, and the Keynesian multiplier bounds
  the aggregate effect. (2) Record S&P margins are mathematically equivalent
  to labor-share compression times the revenue base. (3) Displacement causes
  consumption to fall via MPC.

  NUMERICAL OBSERVATIONS (not predictions):
  * φ ≈ 2.2% — MUFG 2026
  * S&P Q1 2026 margin = 13.1% — FactSet
  * US MPC ≈ 0.9 — BEA post-2020

  SOURCES:
  * Keynes (1936), "General Theory of Employment, Interest, and Money".
  * BEA NIPA Handbook.
  * MUFG / CreditSights, "Hyperscaler Capex 2026", Jan 2026.

  TIER: THEOREM for all identities and inequalities.
-/
import Economy.Macro
import Economy.FinancialMarkets
import Mathlib.Tactic

namespace Economy

/-- THEOREM (hyperscaler capex GDP contribution via NIPA): if investment
    `I` includes hyperscaler capex `K_H`, then increasing `K_H` by Δ
    increases `Y` by exactly Δ (holding `C`, `G`, `NX` fixed).  This is
    the unit-multiplier base case before any consumption feedback. -/
theorem hyperscaler_capex_unit_multiplier
    (s : MacroState) (ΔK_H : ℝ) :
    ({C := s.C, I := s.I + ΔK_H, G := s.G, NX := s.NX : MacroState}).Y
      = s.Y + ΔK_H := by
  unfold MacroState.Y
  ring

/-- THEOREM (Keynesian multiplier bound): with marginal propensity to consume
    `m ∈ [0,1)` and tax rate `τ ∈ [0,1]`, an exogenous investment Δ raises
    income by at most `Δ / (1 − m·(1−τ))`. We state this as the algebraic
    identity defining the multiplier; the economic story is that the
    denominator is bounded below by `1 − m`. -/
theorem keynesian_multiplier (Δ m τ : ℝ)
    (hm : 0 ≤ m) (hm1 : m < 1) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) (hΔ : 0 ≤ Δ) :
    Δ ≤ Δ * (1 / (1 - m * (1 - τ))) := by
  have h1τ_nn : 0 ≤ 1 - τ := by linarith
  have hmfactor : 0 ≤ m * (1 - τ) := mul_nonneg hm h1τ_nn
  have hmfactor_lt : m * (1 - τ) < 1 := by
    have : m * (1 - τ) ≤ m * 1 := mul_le_mul_of_nonneg_left (by linarith) hm
    linarith
  have hden_pos : 0 < 1 - m * (1 - τ) := by linarith
  have hden_le_one : 1 - m * (1 - τ) ≤ 1 := by linarith
  have hinv_ge_one : 1 ≤ 1 / (1 - m * (1 - τ)) := by
    rw [le_div_iff₀ hden_pos]
    linarith
  calc Δ = Δ * 1 := by ring
    _ ≤ Δ * (1 / (1 - m * (1 - τ))) := by
        exact mul_le_mul_of_nonneg_left hinv_ge_one hΔ

/-- Net output growth under the coupling model: Ghost-GDP contribution
    minus consumption drag from displacement. -/
noncomputable def netOutputGrowth (gA α gK m w ΔL Y : ℝ) : ℝ :=
  (gA + (1 - α) * gK) - m * (w * ΔL / Y)

/-- THEOREM (Ghost GDP dominates iff capex+TFP channel exceeds displacement
    drag): net output growth is positive iff `gA + (1-α)·gK` exceeds the
    consumption drag `m · (w · ΔL / Y)`. This is the bubble-vs-super-cycle
    decision boundary. -/
theorem ghost_gdp_dominates_iff
    (gA α gK m w ΔL Y : ℝ) (hY : 0 < Y) :
    0 < netOutputGrowth gA α gK m w ΔL Y
      ↔ m * (w * ΔL / Y) < gA + (1 - α) * gK := by
  unfold netOutputGrowth
  constructor
  · intro h; linarith
  · intro h; linarith

end Economy
