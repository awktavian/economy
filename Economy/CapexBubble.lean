/-
  Economy.CapexBubble — debt-sustainability and bubble-pop dynamics for
  hyperscaler capex.

  ECONOMIC CLAIM: Hyperscaler capex K_H is partially debt-financed. The
  sustainability condition is:

      D · interest ≤ CF_growth

  When the debt service `D · interest` exceeds operating cash flow growth,
  bond markets stop rolling the debt and capex collapses to maintenance-only.
  This shifts the capital growth rate `gK` from the hyperscaler regime
  (≈ 0.005/mo, ≈ 6%/yr) to the maintenance regime (≈ 0.00125/mo, ≈ 1.5%/yr).

  Through the Ghost-GDP identity (Economy.FinanceRealCoupling), the loss to
  GDP growth is `(1-α) · (gK_hyper - gK_maintenance)`, which at α=0.6 and
  the BEA 2026 numbers is `0.4 · 0.00375 ≈ 0.0015/mo ≈ 1.8%/yr`. This is
  the upper bound on the GDP shock from a capex bubble pop, before any
  multiplier or feedback effects.

  SOURCES:
  * Hyman Minsky (1992), "The Financial Instability Hypothesis", Levy Working
    Paper No. 74.
  * MUFG / CreditSights (2026), "Hyperscaler Debt Stack Analysis", Jan 2026:
    estimated $400B aggregate hyperscaler debt against $1.7T market cap.
  * BEA NIPA: maintenance capex ≈ 1.5% annual depreciation rate.

  TIER: THEOREM for all five results below.
-/
import Economy.FinanceRealCoupling
import Economy.Calibration
import Mathlib.Tactic

namespace Economy

noncomputable section

/-! ### Capex parameters -/

/-- Hyperscaler capex sustainability parameters. -/
structure CapexParams where
  /-- Operating cash flow growth rate (per period). -/
  cashFlowGrowth : ℝ
  /-- Aggregate hyperscaler debt stack ($T). -/
  debtStack      : ℝ
  /-- Interest rate on the debt stack (per period). -/
  interestRate   : ℝ
  /-- Hyperscaler capital growth rate (per month). -/
  gK_hyper       : ℝ
  /-- Maintenance-only capital growth rate (per month). -/
  gK_maintenance : ℝ
  cf_nn      : 0 ≤ cashFlowGrowth
  debt_nn    : 0 ≤ debtStack
  rate_nn    : 0 ≤ interestRate
  rate_lt_one : interestRate < 1
  hyper_nn    : 0 ≤ gK_hyper
  maint_nn    : 0 ≤ gK_maintenance
  /-- The hyperscaler regime capital-growth rate is at least the
      maintenance regime (the bubble adds, never subtracts). -/
  hyper_ge_maint : gK_maintenance ≤ gK_hyper

namespace CapexParams

/-- Debt service: `debtStack · interestRate`. -/
def debtService (c : CapexParams) : ℝ := c.debtStack * c.interestRate

theorem debtService_nn (c : CapexParams) : 0 ≤ c.debtService :=
  mul_nonneg c.debt_nn c.rate_nn

/-- Sustainability predicate: debt service is bounded by cash flow growth. -/
def sustainable (c : CapexParams) : Prop :=
  c.debtService ≤ c.cashFlowGrowth

/-- Decidability lifted from `Real.decidableLE` (classical). -/
instance (c : CapexParams) : Decidable c.sustainable := by
  unfold sustainable; exact Classical.propDecidable _

/-- Effective capital growth rate: hyperscaler if sustainable, maintenance
    if not. This is the discontinuous switch the bubble-pop term encodes. -/
noncomputable def effectiveGK (c : CapexParams) : ℝ :=
  if c.sustainable then c.gK_hyper else c.gK_maintenance

theorem effectiveGK_nn (c : CapexParams) : 0 ≤ c.effectiveGK := by
  unfold effectiveGK
  by_cases h : c.sustainable
  · simp [h, c.hyper_nn]
  · simp [h, c.maint_nn]

theorem effectiveGK_le_hyper (c : CapexParams) :
    c.effectiveGK ≤ c.gK_hyper := by
  unfold effectiveGK
  by_cases h : c.sustainable
  · simp [h]
  · simp [h]
    exact c.hyper_ge_maint

theorem effectiveGK_ge_maint (c : CapexParams) :
    c.gK_maintenance ≤ c.effectiveGK := by
  unfold effectiveGK
  by_cases h : c.sustainable
  · simp [h]; exact c.hyper_ge_maint
  · simp [h]

end CapexParams

/-! ### Theorem 1 — sufficient sustainability condition -/

/-- THEOREM (debt_sustainability_sufficient): if debt service is at most
    cash-flow growth, the hyperscaler regime applies and the effective
    capital growth rate equals `gK_hyper`. -/
theorem debt_sustainability_sufficient (c : CapexParams)
    (h : c.debtService ≤ c.cashFlowGrowth) :
    c.effectiveGK = c.gK_hyper := by
  unfold CapexParams.effectiveGK
  have : c.sustainable := h
  simp [this]

/-- THEOREM (debt_failure_collapses_to_maintenance): if debt service exceeds
    cash-flow growth, the effective rate collapses to `gK_maintenance`. -/
theorem debt_failure_collapses_to_maintenance (c : CapexParams)
    (h : c.cashFlowGrowth < c.debtService) :
    c.effectiveGK = c.gK_maintenance := by
  unfold CapexParams.effectiveGK
  have hns : ¬ c.sustainable := by
    unfold CapexParams.sustainable
    exact not_le.mpr h
  simp [hns]

/-! ### Theorem 2 — Ghost GDP loss bound -/

/-- The Ghost GDP contribution from capex: `(1 - α) · gK`. -/
def ghostGDPContribution (α gK : ℝ) : ℝ := (1 - α) * gK

/-- Pop loss to Ghost GDP: how much the (1-α)·gK channel drops when the
    sustainability condition fails and gK switches from hyper to maintenance. -/
def popGhostGDPLoss (c : CapexParams) (α : ℝ) : ℝ :=
  (1 - α) * (c.gK_hyper - c.gK_maintenance)

/-- THEOREM (bubble_pop_ghost_gdp_loss): the loss to the Ghost GDP channel
    when the bubble pops equals `(1-α) · (gK_hyper - gK_maintenance)`,
    which is also the difference between the sustainable and unsustainable
    contributions. -/
theorem bubble_pop_ghost_gdp_loss (c : CapexParams) (α : ℝ) :
    popGhostGDPLoss c α =
      ghostGDPContribution α c.gK_hyper - ghostGDPContribution α c.gK_maintenance := by
  unfold popGhostGDPLoss ghostGDPContribution
  ring

/-! ### Theorem 3 — magnitude bound -/

/-- THEOREM (bubble_pop_magnitude): the GDP shock from a bubble pop is
    bounded above by `(1-α) · gK_hyper`. The bound is tight when
    `gK_maintenance = 0`; under positive maintenance, the realized shock
    is strictly smaller. -/
theorem bubble_pop_magnitude (c : CapexParams) (α : ℝ) (hα : α ≤ 1) :
    popGhostGDPLoss c α ≤ (1 - α) * c.gK_hyper := by
  unfold popGhostGDPLoss
  have h1α : 0 ≤ 1 - α := by linarith
  have hdiff : c.gK_hyper - c.gK_maintenance ≤ c.gK_hyper := by linarith [c.maint_nn]
  exact mul_le_mul_of_nonneg_left hdiff h1α

/-- THEOREM (bubble_pop_magnitude_nn): the pop loss is nonnegative
    (the bubble pop is always a drag on GDP, never a boost). -/
theorem bubble_pop_magnitude_nn (c : CapexParams) (α : ℝ) (hα : α ≤ 1) :
    0 ≤ popGhostGDPLoss c α := by
  unfold popGhostGDPLoss
  have h1α : 0 ≤ 1 - α := by linarith
  have hdiff : 0 ≤ c.gK_hyper - c.gK_maintenance := by linarith [c.hyper_ge_maint]
  exact mul_nonneg h1α hdiff

/-! ### Theorem 4 — connection to FinanceRealCoupling -/

/-- THEOREM (effectiveGK_yields_netOutputGrowth): under any sustainability
    state, the net output growth in `Economy.FinanceRealCoupling`
    evaluated at `effectiveGK` is bounded above by the hyperscaler-regime
    value. The bubble can only reduce the capital channel; everything else
    is held fixed. -/
theorem effectiveGK_yields_netOutputGrowth_bound
    (c : CapexParams) (gA α m w ΔL Y : ℝ) (hα : α ≤ 1) :
    netOutputGrowth gA α c.effectiveGK m w ΔL Y
      ≤ netOutputGrowth gA α c.gK_hyper m w ΔL Y := by
  unfold netOutputGrowth
  have h1α : 0 ≤ 1 - α := by linarith
  have hgK : c.effectiveGK ≤ c.gK_hyper := c.effectiveGK_le_hyper
  have : (1 - α) * c.effectiveGK ≤ (1 - α) * c.gK_hyper :=
    mul_le_mul_of_nonneg_left hgK h1α
  linarith

/-! ### Theorem 5 — BEA 2026 calibration -/

/-- BEA / MUFG / CreditSights 2026 calibration: $400B debt at 5%/yr
    (≈ 0.00417/mo), cash flow growth ≈ 0.005/mo (sustainable today),
    hyperscaler gK ≈ 0.005/mo, maintenance gK ≈ 0.00125/mo. -/
def capexBEA2026 : CapexParams where
  cashFlowGrowth := 5 / 1000
  debtStack := 4 / 10        -- $0.4T
  interestRate := 5 / 1000   -- 0.5%/mo (≈ 6%/yr)
  gK_hyper := 5 / 1000
  gK_maintenance := 125 / 100000   -- 0.00125/mo
  cf_nn := by norm_num
  debt_nn := by norm_num
  rate_nn := by norm_num
  rate_lt_one := by norm_num
  hyper_nn := by norm_num
  maint_nn := by norm_num
  hyper_ge_maint := by norm_num

/-- THEOREM (capexBEA_today_sustainable): under the BEA 2026 numbers, debt
    service ($0.4T · 0.005 = $0.002T/mo = 0.2%/mo) is below cash flow
    growth (0.5%/mo). The hyperscaler regime applies today. -/
theorem capexBEA_today_sustainable :
    capexBEA2026.sustainable := by
  unfold CapexParams.sustainable CapexParams.debtService capexBEA2026
  norm_num

/-- THEOREM (capexBEA_pop_loss_36mo): the GDP shock from a hypothetical
    pop of the BEA 2026 hyperscaler stack is bounded above by
    (1 - 0.6) · (0.005 - 0.00125) = 0.0015/mo, or about 1.8% per year. -/
theorem capexBEA_pop_loss_monthly :
    popGhostGDPLoss capexBEA2026 (6 / 10) = 15 / 10000 := by
  unfold popGhostGDPLoss capexBEA2026
  norm_num

end

end Economy
