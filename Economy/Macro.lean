/-
  Economy.Macro
  Macroeconomic identities: NIPA, factor income, Solow residual, Ghost GDP.

  ECONOMIC CLAIM: Under Cobb-Douglas Y = A · K^(1-α) · L^α with competitive
  factor markets and constant returns to scale, the NIPA expenditure identity
  Y = C + I + G + NX is structural, the factor income identity
  Y = wL + rK follows from Euler's theorem on homogeneous functions (applied
  to a two-factor case below), the labor share equals α exactly, and the
  Solow residual identifies TFP growth.

  "Ghost GDP" (2026 press): GDP grows with constant labor when TFP growth +
  (1−α) · (capital growth) > 0. Hyperscaler capex ($602B, ~2.2% of US GDP
  in 2026) drives the K term; AI-driven productivity drives the TFP term.

  SOURCES:
  * Cobb & Douglas (1928), "A Theory of Production", AER 18(1): 139–165.
  * Solow (1957), "Technical Change and the Aggregate Production Function",
    RESTAT 39(3): 312–320. https://doi.org/10.2307/1926047
  * BEA NIPA Handbook, Ch. 2 (expenditure identity).
  * BLS Productivity and Costs, Q1 2026 (Ghost GDP narrative).

  TIER: THEOREM for identities and structural inequalities; FRAMEWORK for the
  Cobb-Douglas functional form itself (which is a modeling choice, not a theorem).
  The `SolowGrowth` results are proved relative to the structure field
  `solow_id`. For `CobbDouglas` output paths the field is DERIVED, not assumed
  (`SolowGrowth.ofCobbDouglasPaths`): the log-growth identity is exact for
  instantaneous (log-derivative) rates — no linearization remainder. It is
  approximate only when log rates are replaced by simple relative changes,
  which is not formalized here.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

namespace Economy

open Real

/-- Macroeconomic state at a point in time. The expenditure identity
    `Y = C + I + G + NX` is BUILT IN via the definition of `Y`. -/
structure MacroState where
  C : ℝ       -- consumption
  I : ℝ       -- investment
  G : ℝ       -- government spending
  NX : ℝ      -- net exports

namespace MacroState

/-- GDP from the expenditure side (definitional NIPA). -/
def Y (s : MacroState) : ℝ := s.C + s.I + s.G + s.NX

end MacroState

/-- Cobb-Douglas production with capital share `1-α` and labor share `α`.
    Y = A · K^(1-α) · L^α, with A > 0, K ≥ 0, L ≥ 0, α ∈ (0,1). -/
structure CobbDouglas where
  A : ℝ          -- total factor productivity
  K : ℝ          -- capital stock
  L : ℝ          -- labor input
  α : ℝ          -- labor share
  A_pos : 0 < A
  K_nn : 0 ≤ K
  L_nn : 0 ≤ L
  α_pos : 0 < α
  α_lt_one : α < 1

namespace CobbDouglas

/-- Output `Y = A · K^(1-α) · L^α`. -/
noncomputable def Y (p : CobbDouglas) : ℝ := p.A * p.K ^ (1 - p.α) * p.L ^ p.α

/-- THEOREM: output is nonnegative. -/
theorem Y_nonneg (p : CobbDouglas) : 0 ≤ p.Y := by
  unfold Y
  have : 0 ≤ p.K ^ (1 - p.α) := Real.rpow_nonneg p.K_nn _
  have : 0 ≤ p.L ^ p.α := Real.rpow_nonneg p.L_nn _
  have : 0 ≤ p.A * p.K ^ (1 - p.α) :=
    mul_nonneg p.A_pos.le (Real.rpow_nonneg p.K_nn _)
  exact mul_nonneg this (Real.rpow_nonneg p.L_nn _)

/-- THEOREM (Euler / homogeneity of degree 1): scaling both inputs by `λ > 0`
    scales output by `λ`. This is CRS. -/
theorem Y_crs (p : CobbDouglas) (lam : ℝ) (hlam : 0 < lam) :
    (p.A * (lam * p.K) ^ (1 - p.α) * (lam * p.L) ^ p.α)
      = lam * p.Y := by
  unfold Y
  have hK : 0 ≤ p.K := p.K_nn
  have hL : 0 ≤ p.L := p.L_nn
  have hlam_nn : 0 ≤ lam := hlam.le
  rw [Real.mul_rpow hlam_nn hK, Real.mul_rpow hlam_nn hL]
  have hprod : lam ^ (1 - p.α) * lam ^ p.α = lam := by
    rw [← Real.rpow_add hlam]
    have : 1 - p.α + p.α = 1 := by ring
    rw [this, Real.rpow_one]
  calc p.A * (lam ^ (1 - p.α) * p.K ^ (1 - p.α)) * (lam ^ p.α * p.L ^ p.α)
      = p.A * (p.K ^ (1 - p.α) * p.L ^ p.α) * (lam ^ (1 - p.α) * lam ^ p.α) := by ring
    _ = p.A * (p.K ^ (1 - p.α) * p.L ^ p.α) * lam := by rw [hprod]
    _ = lam * (p.A * p.K ^ (1 - p.α) * p.L ^ p.α) := by ring

/-- THEOREM: output is strictly positive once both inputs are strictly
    positive (the carrier only gives `K ≥ 0`, `L ≥ 0`). -/
theorem Y_pos (p : CobbDouglas) (hK : 0 < p.K) (hL : 0 < p.L) : 0 < p.Y := by
  unfold Y
  exact mul_pos (mul_pos p.A_pos (Real.rpow_pos_of_pos hK _))
    (Real.rpow_pos_of_pos hL _)

/-- Output viewed as a function of labor, capital fixed. -/
noncomputable def outputOfLabor (p : CobbDouglas) (ℓ : ℝ) : ℝ :=
  p.A * p.K ^ (1 - p.α) * ℓ ^ p.α

/-- Output viewed as a function of capital, labor fixed. -/
noncomputable def outputOfCapital (p : CobbDouglas) (κ : ℝ) : ℝ :=
  p.A * κ ^ (1 - p.α) * p.L ^ p.α

/-- THEOREM (marginal product of labor): for the Cobb-Douglas production
    function, `∂Y/∂L = α · Y/L`. This is differentiation of `rpow`, not an
    assumption: it is what licenses reading `w = α·Y/L` as the competitive wage
    in `ofCompetitivePrices`. -/
theorem hasDerivAt_outputOfLabor (p : CobbDouglas) (hL : 0 < p.L) :
    HasDerivAt p.outputOfLabor (p.α * p.Y / p.L) p.L := by
  have h : HasDerivAt (fun ℓ : ℝ => ℓ ^ p.α) (p.α * p.L ^ (p.α - 1)) p.L :=
    Real.hasDerivAt_rpow_const (Or.inl hL.ne')
  have h2 : HasDerivAt (fun y : ℝ => p.A * p.K ^ (1 - p.α) * y ^ p.α)
      (p.A * p.K ^ (1 - p.α) * (p.α * p.L ^ (p.α - 1))) p.L :=
    h.const_mul (p.A * p.K ^ (1 - p.α))
  refine h2.congr_deriv ?_
  unfold Y
  rw [Real.rpow_sub_one hL.ne']
  field_simp

/-- THEOREM (marginal product of capital): `∂Y/∂K = (1-α) · Y/K`. -/
theorem hasDerivAt_outputOfCapital (p : CobbDouglas) (hK : 0 < p.K) :
    HasDerivAt p.outputOfCapital ((1 - p.α) * p.Y / p.K) p.K := by
  have h : HasDerivAt (fun κ : ℝ => κ ^ (1 - p.α)) ((1 - p.α) * p.K ^ (1 - p.α - 1)) p.K :=
    Real.hasDerivAt_rpow_const (Or.inl hK.ne')
  have h2 : HasDerivAt (fun y : ℝ => p.A * y ^ (1 - p.α) * p.L ^ p.α)
      (p.A * ((1 - p.α) * p.K ^ (1 - p.α - 1)) * p.L ^ p.α) p.K :=
    (h.const_mul p.A).mul_const (p.L ^ p.α)
  refine h2.congr_deriv ?_
  unfold Y
  rw [Real.rpow_sub_one hK.ne']
  field_simp

/-- The Cobb-Douglas output law as a FUNCTION of factor paths:
    `(pathsOutput p A K L) s = A s · K s ^ (1-α) · L s ^ α`, with the labor
    share taken from the carrier `p`. At constant paths it is `CobbDouglas.Y`. -/
noncomputable def pathsOutput (p : CobbDouglas) (A K L : ℝ → ℝ) : ℝ → ℝ :=
  fun s => A s * K s ^ (1 - p.α) * L s ^ p.α

end CobbDouglas

/-- Factor payments in a competitive Cobb-Douglas economy. Given the first-order
    conditions `w = MPL = α Y/L` and `r = MPK = (1-α) Y/K`, factor income
    `wL + rK = α Y + (1-α) Y = Y`. -/
structure FactorIncome where
  Y : ℝ
  w : ℝ
  r : ℝ
  L : ℝ
  K : ℝ
  α : ℝ
  /-- First-order condition for labor: `wL = αY`. -/
  foc_labor : w * L = α * Y
  /-- First-order condition for capital: `rK = (1-α)Y`. -/
  foc_capital : r * K = (1 - α) * Y

namespace FactorIncome

/-- THEOREM (factor income identity via Euler's theorem): under CRS Cobb-Douglas
    first-order conditions, labor + capital income exhaust output. This is
    non-trivial: it's the finite-dimensional Euler identity `f = ∑ xᵢ · ∂f/∂xᵢ`
    specialized to Cobb-Douglas. -/
theorem factor_income_exhausts (f : FactorIncome) : f.w * f.L + f.r * f.K = f.Y := by
  rw [f.foc_labor, f.foc_capital]
  ring

/-- THEOREM (labor share = α): under FOC, `wL/Y = α` whenever `Y ≠ 0`. -/
theorem labor_share_equals_alpha (f : FactorIncome) (hY : f.Y ≠ 0) :
    f.w * f.L / f.Y = f.α := by
  rw [f.foc_labor]
  field_simp

/-- THEOREM (capital share = 1−α): symmetric. -/
theorem capital_share_equals_one_minus_alpha (f : FactorIncome) (hY : f.Y ≠ 0) :
    f.r * f.K / f.Y = 1 - f.α := by
  rw [f.foc_capital]
  field_simp

end FactorIncome

/-! ### Competitive factor income DERIVED from Cobb-Douglas -/

/-- Competitive factor payments for a Cobb-Douglas economy with strictly
    positive inputs: pay each factor its marginal product
    (`CobbDouglas.hasDerivAt_outputOfLabor` / `...Capital`). The
    `FactorIncome` fields `foc_labor` / `foc_capital` are then DERIVED, not
    assumed: this construction is what shows the first-order-condition bundle
    is inhabited by genuine production-function data rather than being a
    wrapper that assumes its conclusion. -/
noncomputable def ofCompetitivePrices (p : CobbDouglas) (hK : 0 < p.K) (hL : 0 < p.L) :
    FactorIncome where
  Y := p.Y
  w := p.α * p.Y / p.L
  r := (1 - p.α) * p.Y / p.K
  L := p.L
  K := p.K
  α := p.α
  foc_labor := by field_simp [hL.ne']
  foc_capital := by field_simp [hK.ne']

/-- THEOREM (Euler for Cobb-Douglas, consumed): under competitive pricing,
    labor income plus capital income exhausts output — obtained by applying
    `FactorIncome.factor_income_exhausts` to the derived instance. -/
theorem cobbDouglas_factor_income_exhausts (p : CobbDouglas)
    (hK : 0 < p.K) (hL : 0 < p.L) :
    let f := ofCompetitivePrices p hK hL
    f.w * f.L + f.r * f.K = f.Y :=
  FactorIncome.factor_income_exhausts _

/-- THEOREM (labor share = α, consumed): the competitive labor share of a
    Cobb-Douglas economy is exactly `α` — `FactorIncome.labor_share_equals_alpha`
    applied at the derived instance; strict positivity of `Y` comes from
    `CobbDouglas.Y_pos`. -/
theorem cobbDouglas_labor_share (p : CobbDouglas) (hK : 0 < p.K) (hL : 0 < p.L) :
    let f := ofCompetitivePrices p hK hL
    f.w * f.L / f.Y = f.α :=
  FactorIncome.labor_share_equals_alpha _ (CobbDouglas.Y_pos p hK hL).ne'

/-- THEOREM (the wage IS the marginal product): `deriv (outputOfLabor p) p.L`
    equals the `w` field of the constructed `FactorIncome` — the bridge that
    makes `ofCompetitivePrices` an economic construction rather than an
    algebraic relabeling. -/
theorem cobbDouglas_w_is_mpl (p : CobbDouglas) (hK : 0 < p.K) (hL : 0 < p.L) :
    deriv p.outputOfLabor p.L = (ofCompetitivePrices p hK hL).w :=
  (p.hasDerivAt_outputOfLabor hL).deriv

/-- THEOREM (the rental rate IS the marginal product). -/
theorem cobbDouglas_r_is_mpk (p : CobbDouglas) (hK : 0 < p.K) (hL : 0 < p.L) :
    deriv p.outputOfCapital p.K = (ofCompetitivePrices p hK hL).r :=
  (p.hasDerivAt_outputOfCapital hK).deriv

/-- Solow-residual growth accounting.
    Given log-differences (`g` = growth rate) of TFP, capital, labor, output,
    and labor share α, the Solow identity is
      `gY = gA + (1-α) gK + α gL`,
    i.e., TFP growth = output growth − (1-α) · capital growth − α · labor growth. -/
structure SolowGrowth where
  gY : ℝ
  gA : ℝ
  gK : ℝ
  gL : ℝ
  α : ℝ
  /-- Solow identity (linearization of log Cobb-Douglas). -/
  solow_id : gY = gA + (1 - α) * gK + α * gL

namespace SolowGrowth

/-- THEOREM (Solow residual): TFP growth is identified by
    `gA = gY − (1-α) gK − α gL`. -/
theorem solow_residual (s : SolowGrowth) :
    s.gA = s.gY - (1 - s.α) * s.gK - s.α * s.gL := by
  have := s.solow_id
  linarith

/-- CONDITIONAL THEOREM (Ghost GDP under the assumed Solow identity): with
    constant labor (`gL = 0`), output growth equals TFP growth plus
    `(1-α) · capital growth`. Conditional on `SolowGrowth.solow_id` — the
    log-linearized identity `gY = gA + (1-α)·gK + α·gL`, which is an ASSUMED
    structure field here, not derived from `CobbDouglas.Y` in this file.
    Given that assumption, the proof is substitution of `gL = 0` plus
    `linarith`. This is the 2026 "Ghost GDP" narrative, conditional on the
    log-linearization. -/
theorem ghost_gdp_constant_labor (s : SolowGrowth) (hL : s.gL = 0) :
    s.gY = s.gA + (1 - s.α) * s.gK := by
  have h := s.solow_id
  rw [hL] at h
  linarith

/-- THEOREM (Ghost GDP lower bound ≥ 0): with constant labor, if TFP and
    capital both grow non-negatively and α < 1, Y grows non-negatively.
    The hyperscaler $602B capex channel is the K term; AI productivity is A. -/
theorem ghost_gdp_nonneg (s : SolowGrowth)
    (hL : s.gL = 0) (hA : 0 ≤ s.gA) (hK : 0 ≤ s.gK) (hα : s.α ≤ 1) :
    0 ≤ s.gY := by
  rw [ghost_gdp_constant_labor s hL]
  have h1 : 0 ≤ 1 - s.α := by linarith
  have h2 : 0 ≤ (1 - s.α) * s.gK := mul_nonneg h1 hK
  linarith

end SolowGrowth

/-! ### Solow identity DERIVED from Cobb-Douglas factor paths -/

namespace SolowGrowth

/-- THEOREM (log-growth decomposition of Cobb-Douglas, exact): if the output
    path is the CD law `CobbDouglas.pathsOutput p A K L`, and the factor paths
    are differentiable at `t` with strictly positive values there, then the
    log-derivative (instantaneous growth) of output splits exactly:
    `d/dt log Y = A'/A + (1-α)·K'/K + α·L'/L`.

    Exactness note (truth-check): passing to logarithms converts the CD
    PRODUCT into a SUM pointwise (`Real.log_mul`, `Real.log_rpow`), so
    differentiating loses nothing — this is NOT a first-order linearization.
    The usual "≈" of growth accounting appears only when the log-rates
    `A'/A` are replaced by simple relative changes; that replacement is
    unformalized here. -/
theorem cobbDouglas_growth_identity (p : CobbDouglas) (A K L Y : ℝ → ℝ) (t : ℝ)
    (hY : ∀ s, Y s = p.pathsOutput A K L s)
    (hA0 : 0 < A t) (hK0 : 0 < K t) (hL0 : 0 < L t)
    (dA : DifferentiableAt ℝ A t) (dK : DifferentiableAt ℝ K t)
    (dL : DifferentiableAt ℝ L t) :
    HasDerivAt (fun s => Real.log (Y s))
      (deriv A t / A t + (1 - p.α) * (deriv K t / K t) + p.α * (deriv L t / L t)) t := by
  have hAn : ∀ᶠ s in nhds t, 0 < A s := dA.continuousAt.eventually (isOpen_Ioi.mem_nhds hA0)
  have hKn : ∀ᶠ s in nhds t, 0 < K s := dK.continuousAt.eventually (isOpen_Ioi.mem_nhds hK0)
  have hLn : ∀ᶠ s in nhds t, 0 < L s := dL.continuousAt.eventually (isOpen_Ioi.mem_nhds hL0)
  have hYt : 0 < Y t := by
    rw [hY t, CobbDouglas.pathsOutput]
    exact mul_pos (mul_pos hA0 (Real.rpow_pos_of_pos hK0 _)) (Real.rpow_pos_of_pos hL0 _)
  have hlog : (fun s => Real.log (Y s)) =ᶠ[nhds t]
      fun s => Real.log (A s) + (1 - p.α) * Real.log (K s) + p.α * Real.log (L s) := by
    filter_upwards [hAn, hKn, hLn] with s hA hK hL
    have h2 : 0 < K s ^ (1 - p.α) * L s ^ p.α :=
      mul_pos (Real.rpow_pos_of_pos hK _) (Real.rpow_pos_of_pos hL _)
    calc Real.log (Y s)
        = Real.log (A s * (K s ^ (1 - p.α) * L s ^ p.α)) := by
            rw [hY s, CobbDouglas.pathsOutput, (mul_assoc _ _ _).symm]
      _ = Real.log (A s) + Real.log (K s ^ (1 - p.α) * L s ^ p.α) :=
            Real.log_mul (ne_of_gt hA) (ne_of_gt h2)
      _ = Real.log (A s) + (Real.log (K s ^ (1 - p.α)) + Real.log (L s ^ p.α)) := by
            rw [Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos hK _))
              (ne_of_gt (Real.rpow_pos_of_pos hL _))]
      _ = (Real.log (A s) + (1 - p.α) * Real.log (K s)) + p.α * Real.log (L s) := by
            rw [Real.log_rpow hK _, Real.log_rpow hL _, ← add_assoc]
  have dY : DifferentiableAt ℝ Y t := by
    have hcd : DifferentiableAt ℝ (p.pathsOutput A K L) t := by
      unfold CobbDouglas.pathsOutput
      refine DifferentiableAt.mul (DifferentiableAt.mul dA ?_) ?_
      · exact ((Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hK0))).comp t dK.hasDerivAt).differentiableAt
      · exact ((Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hL0))).comp t dL.hasDerivAt).differentiableAt
    exact hcd.congr_of_eventuallyEq
      (Filter.eventually_of_mem Filter.univ_mem (fun s _ => hY s))
  have hA' : HasDerivAt (fun s => Real.log (A s)) (deriv A t / A t) t :=
    (dA.hasDerivAt).log (ne_of_gt hA0)
  have hK' : HasDerivAt (fun s => Real.log (K s)) (deriv K t / K t) t :=
    (dK.hasDerivAt).log (ne_of_gt hK0)
  have hL' : HasDerivAt (fun s => Real.log (L s)) (deriv L t / L t) t :=
    (dL.hasDerivAt).log (ne_of_gt hL0)
  have hrhs : HasDerivAt
      (fun s => Real.log (A s) + (1 - p.α) * Real.log (K s) + p.α * Real.log (L s))
      (deriv A t / A t + (1 - p.α) * (deriv K t / K t) + p.α * (deriv L t / L t)) t :=
    (hA'.add (hK'.const_mul (1 - p.α))).add (hL'.const_mul p.α)
  exact hrhs.congr_of_eventuallyEq hlog

/-- A `SolowGrowth` instance produced from Cobb-Douglas factor paths: the four
    growth rates are the instantaneous log-derivatives of the factor and output
    paths at `t`, and the assumed structure field `solow_id` is DERIVED from
    `cobbDouglas_growth_identity` rather than supplied. `gY` is deliberately
    defined as the quotient `deriv Y t / Y t`, not as the sum, so the identity
    carries proof content. No bounds on `p.α` are needed: the field
    `SolowGrowth.α : ℝ` is unconstrained. -/
noncomputable def ofCobbDouglasPaths (p : CobbDouglas) (A K L Y : ℝ → ℝ) (t : ℝ)
    (hY : ∀ s, Y s = p.pathsOutput A K L s)
    (hA0 : 0 < A t) (hK0 : 0 < K t) (hL0 : 0 < L t)
    (dA : DifferentiableAt ℝ A t) (dK : DifferentiableAt ℝ K t)
    (dL : DifferentiableAt ℝ L t) : SolowGrowth where
  gY := deriv Y t / Y t
  gA := deriv A t / A t
  gK := deriv K t / K t
  gL := deriv L t / L t
  α := p.α
  solow_id := by
    have hYt : 0 < Y t := by
      rw [hY t, CobbDouglas.pathsOutput]
      exact mul_pos (mul_pos hA0 (Real.rpow_pos_of_pos hK0 _)) (Real.rpow_pos_of_pos hL0 _)
    have dY : DifferentiableAt ℝ Y t := by
      have hcd : DifferentiableAt ℝ (p.pathsOutput A K L) t := by
        unfold CobbDouglas.pathsOutput
        refine DifferentiableAt.mul (DifferentiableAt.mul dA ?_) ?_
        · exact ((Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hK0))).comp t
            dK.hasDerivAt).differentiableAt
        · exact ((Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hL0))).comp t
            dL.hasDerivAt).differentiableAt
      exact hcd.congr_of_eventuallyEq
        (Filter.eventually_of_mem Filter.univ_mem (fun s _ => hY s))
    exact HasDerivAt.unique ((dY.hasDerivAt).log (ne_of_gt hYt))
      (cobbDouglas_growth_identity p A K L Y t hY hA0 hK0 hL0 dA dK dL)

/-- CONSUMPTION 1: the TFP-residual formula `SolowGrowth.solow_residual`
    applied to the DERIVED instance — TFP growth equals the output log-rate
    minus factor-share contributions, now for actual CD paths, no assumption. -/
theorem solow_residual_ofCobbDouglasPaths (p : CobbDouglas) (A K L Y : ℝ → ℝ) (t : ℝ)
    (hY : ∀ s, Y s = p.pathsOutput A K L s)
    (hA0 : 0 < A t) (hK0 : 0 < K t) (hL0 : 0 < L t)
    (dA : DifferentiableAt ℝ A t) (dK : DifferentiableAt ℝ K t)
    (dL : DifferentiableAt ℝ L t) :
    deriv A t / A t = deriv Y t / Y t
      - (1 - p.α) * (deriv K t / K t) - p.α * (deriv L t / L t) := by
  exact solow_residual (ofCobbDouglasPaths p A K L Y t hY hA0 hK0 hL0 dA dK dL)

/-- CONSUMPTION 2: the ghost-GDP corollary `SolowGrowth.ghost_gdp_constant_labor`
    at the DERIVED instance: if the labor path is stationary at `t`
    (`deriv L t = 0`), the output log-rate equals TFP log-rate plus the
    capital-share term — with `solow_id` derived, not assumed. -/
theorem ghost_gdp_ofCobbDouglasPaths (p : CobbDouglas) (A K L Y : ℝ → ℝ) (t : ℝ)
    (hY : ∀ s, Y s = p.pathsOutput A K L s)
    (hA0 : 0 < A t) (hK0 : 0 < K t) (hL0 : 0 < L t)
    (dA : DifferentiableAt ℝ A t) (dK : DifferentiableAt ℝ K t)
    (dL : DifferentiableAt ℝ L t) (hstat : deriv L t = 0) :
    deriv Y t / Y t = deriv A t / A t + (1 - p.α) * (deriv K t / K t) := by
  have hgL : (ofCobbDouglasPaths p A K L Y t hY hA0 hK0 hL0 dA dK dL).gL = 0 := by
    show deriv L t / L t = 0
    rw [hstat]
    exact zero_div _
  exact ghost_gdp_constant_labor _ hgL

end SolowGrowth

end Economy
