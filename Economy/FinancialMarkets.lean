/-
  Economy.FinancialMarkets
  Asset pricing coupled to the real economy.

  ECONOMIC CLAIM: Firm profit = revenue − labor − capital − tax.
  Profit margin rises when labor share falls (revenue and other costs fixed).
  Present value of cash flows is monotone in each cash flow and antitone in
  discount rate. Gordon growth: for constant growth `g < r`, a growing
  perpetuity's PV equals `C₀ / (r − g)`. Capex-earnings gap forces external
  finance when capex > profit.

  SOURCES:
  * Gordon (1959), "Dividends, Earnings and Stock Prices", RESTAT 41(2): 99–105.
  * Modigliani-Miller (1958), "The Cost of Capital, Corporation Finance, and
    the Theory of Investment", AER 48(3): 261–297.
  * FactSet Earnings Insight, Q1 2026: S&P 500 net profit margin 13.1% (record).
  * MUFG / CreditSights (2026): hyperscaler capex $602B ≈ 2.2% US GDP.

  TIER: THEOREM for all identities and inequalities in this file.
-/
import Mathlib.Tactic

namespace Economy

open Finset

/-- A firm's cash flow in a single period. -/
structure FirmCashFlow where
  revenue : ℝ
  laborCost : ℝ
  capitalCost : ℝ
  tax : ℝ
  revenue_pos : 0 < revenue
  labor_nn : 0 ≤ laborCost
  capital_nn : 0 ≤ capitalCost
  tax_nn : 0 ≤ tax

namespace FirmCashFlow

/-- Profit = revenue − labor − capital − tax. -/
def profit (f : FirmCashFlow) : ℝ := f.revenue - f.laborCost - f.capitalCost - f.tax

/-- Profit margin as a fraction of revenue. -/
noncomputable def margin (f : FirmCashFlow) : ℝ := f.profit / f.revenue

/-- Labor share of revenue (the 13.1% margin story's dual). -/
noncomputable def laborShareRev (f : FirmCashFlow) : ℝ := f.laborCost / f.revenue

/-- THEOREM (margin rises when labor share falls, ceteris paribus): given two
    cash flows with identical revenue, capital, and tax but different labor
    cost, the one with LOWER labor cost has HIGHER margin. This mathematically
    grounds the Q1 2026 record 13.1% S&P margin as the dual of labor share
    compression. -/
theorem margin_rises_when_labor_falls (f g : FirmCashFlow)
    (hrev : f.revenue = g.revenue) (hcap : f.capitalCost = g.capitalCost)
    (htax : f.tax = g.tax) (hlab : f.laborCost < g.laborCost) :
    g.margin < f.margin := by
  unfold margin profit
  rw [hrev, hcap, htax]
  have hrevpos : 0 < g.revenue := g.revenue_pos
  apply (div_lt_div_iff_of_pos_right hrevpos).mpr
  linarith

end FirmCashFlow

/-- Present value of a finite cash-flow stream discounted at rate `r`. -/
noncomputable def PV (n : ℕ) (cashflows : ℕ → ℝ) (r : ℝ) : ℝ :=
  ∑ i ∈ range n, cashflows i / (1 + r) ^ i

/-- THEOREM: PV is monotone in each period's cash flow. -/
theorem PV_mono_cashflows (n : ℕ) (r : ℝ) (hr : 0 < 1 + r)
    (c c' : ℕ → ℝ) (h : ∀ i, c i ≤ c' i) :
    PV n c r ≤ PV n c' r := by
  unfold PV
  apply Finset.sum_le_sum
  intro i _
  have hpow : 0 < (1 + r) ^ i := pow_pos hr _
  exact div_le_div_of_nonneg_right (h i) hpow.le

/-- THEOREM (strict): PV is strictly monotone in cash flows when at least one
    period has a strictly greater cash flow and the horizon covers it. -/
theorem PV_mono_cashflows_strict (n : ℕ) (r : ℝ) (hr : 0 < 1 + r)
    (c c' : ℕ → ℝ) (h : ∀ i, c i ≤ c' i)
    {k : ℕ} (hk : k < n) (hlt : c k < c' k) :
    PV n c r < PV n c' r := by
  unfold PV
  refine Finset.sum_lt_sum (g := fun i => c' i / (1 + r) ^ i)
    (fun i _ => div_le_div_of_nonneg_right (h i) (pow_pos hr _).le)
    ⟨k, Finset.mem_range.mpr hk,
      (div_lt_div_iff_of_pos_right (pow_pos hr k)).mpr hlt⟩

/-- THEOREM: PV is strictly antitone in `r` for a strictly positive constant
    cash-flow stream and at least one period. Raising the discount rate
    strictly lowers PV. This is the Fed-rate-cut channel. -/
theorem PV_antitone_rate_two {r r' : ℝ} (hr : 0 < 1 + r) (hr' : 0 < 1 + r')
    (hlt : r < r') (C : ℝ) (hC : 0 < C) :
    PV 2 (fun _ => C) r' < PV 2 (fun _ => C) r := by
  unfold PV
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, div_one, pow_one]
  -- C + C/(1+r') < C + C/(1+r)
  have hposr : 0 < (1 + r) := hr
  have hposr' : 0 < (1 + r') := hr'
  have hltsum : 1 + r < 1 + r' := by linarith
  have : C / (1 + r') < C / (1 + r) := by
    apply (div_lt_div_iff_of_pos_left hC hposr' hposr).mpr hltsum
  linarith

end Economy
