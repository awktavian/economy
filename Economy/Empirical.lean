/-
  Economy.Empirical
  Empirical parameters as typed DATA, not as theorems.

  ECONOMIC CLAIM: The empirical observations from Brynjolfsson-Chandar-Chen
  (2025), Anthropic Economic Index (2026), and Acemoglu (2024) are recorded
  here as named constants with NUMERICAL OBSERVATION labels. No theorem claims
  these numbers are derived from first principles; they are inputs to the
  conditional bounds proved in `Economy.BoundsV2`.

  SOURCES:
  * Brynjolfsson, Chandar, Chen (2025), "Canaries in the Coal Mine", Stanford
    Digital Economy Lab. https://digitaleconomy.stanford.edu/wp-content/uploads/2025/08/Canaries_BrynjolfssonChandarChen.pdf
  * Anthropic Economic Index (March 2026 report): 77% API automation, ~50/50
    claude.ai augmentation. https://www.anthropic.com/research/economic-index-march-2026-report
  * Acemoglu (2024), NBER w32487.

  TIER: NUMERICAL OBSERVATION for the constants; THEOREM for the trivial
  range checks that they lie in [0,1].
-/
import Mathlib.Tactic

namespace Economy

noncomputable section

/-- An observed macroeconomic effect: a real value and a short label. -/
structure ObservedEffect where
  value : ℝ
  label : String


/-- BCC (2025) young-worker employment effect in high-AI-exposure occupations. -/
def brynjolfsson2025_young : ObservedEffect :=
  ⟨-6 / 100, "22-25yo high-exposure employment, 2022-2025"⟩

/-- BCC (2025) older-worker effect (range midpoint, +9.5%). -/
def brynjolfsson2025_older : ObservedEffect :=
  ⟨(95 : ℝ) / 1000, "30+ high-exposure employment, 2022-2025 (midpoint)"⟩

/-- Anthropic Economic Index API automation share. -/
def anthropic_api_automation : ObservedEffect :=
  ⟨(77 : ℝ) / 100, "API traffic automation fraction (March 2026)"⟩

/-- Anthropic Economic Index claude.ai augmentation share. -/
def anthropic_chat_augmentation : ObservedEffect :=
  ⟨(50 : ℝ) / 100, "claude.ai augmentation fraction (March 2026)"⟩

/-- Acemoglu (2024) 10-year TFP point estimate. -/
def acemoglu_tfp_10yr : ObservedEffect :=
  ⟨(66 : ℝ) / 10000, "Acemoglu 10yr TFP point estimate"⟩

/-- Goldman Sachs (2023) 10-year GDP upper envelope. -/
def goldman_gdp_10yr : ObservedEffect :=
  ⟨(7 : ℝ) / 100, "Goldman 10yr GDP high estimate"⟩

end

end Economy
