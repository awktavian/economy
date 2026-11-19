/-
  Economy.CalibrationPins

  REGRESSION SURFACE for `Economy/Calibration.lean`. A census of the corpus
  (`git grep -l -F <name> -- '*.lean' | wc -l`, run at the base commit) showed
  29 of the 34 declarations in `Calibration.lean` — every V1–V6 validation,
  every E1–E7 edge case, every S1–S5 sensitivity theorem, every C1–C4
  consistency check and all four scenario-bridge theorems — had exactly one
  referring file: the one that declares them. They compiled and nothing
  consumed them, so an edit to a calibration literal could be merged with the
  published receipt left untouched.

  This module is that consumer. It adds no mathematics: every positive leg is
  `Calibration`'s own theorem applied to concrete data, with the statement
  re-authored HERE at the literals. That is what makes it a check.
  `Calibration`'s statement and this leg's statement are now two independent
  copies of the same number, so moving either one stops the leg typechecking
  and `lake build Economy` goes red — the same discipline the corpus already
  uses for `recessionBEA2026_matches_calibration`,
  `capexBEA2026_matches_calibration` and `jobSwapBEA2026_matches_calibration`,
  which the calibration header describes as "agreement checks, not
  validations". Where the corpus already carries a NAMED literal
  (`tfpGoldmanCorner`, `twoClassBEA`, `metrFastScenario`, `acemoglu_tfp_10yr`)
  the leg reads it through that name instead of retyping it, so the pin
  couples two files rather than restating one.

  POSITIVE LEGS. Three of the validations take their parameters as
  hypotheses (V1, V2, V4), so applying them at the anchor forces the literals
  to agree: `validation_goldman_high tfpGoldmanCorner rfl rfl rfl` only
  typechecks while `Productivity`'s corner still reads 0.40 and 0.175 with
  zero friction. The rest evaluate the calibration layer at the three
  canonical calibrations: doubling times 4, 7 and 4 months, saturation
  exposure 1, base exposure `H_min / H_max` equal to 1/12, the bridge's six
  data legs, and fast-over-baseline GDP dominance at the 24-month METR
  horizon.

  NEGATIVE CONTROLS. A leg that only re-proves what its theorem says would
  still pass on a degenerate model, so each family carries at least one
  literal that must NOT satisfy its predicate, proved through the repo's own
  API:
    * V — `deltaTFP tfpGoldmanCorner ≤ 66/10000` is FALSE, by
      `deltaTFP_tfpGoldmanCorner`. The Acemoglu and Goldman anchors are 0.66%
      and 7% apart exactly because the model output moves with the inputs; a
      pin that could not tell them apart would pin nothing. And a firm one
      point of revenue over V4's labor ceiling (56% instead of 55%) has a
      12.1% margin, under the cited 13.1%.
    * E — a factor-income point with `L ≠ 0` has `r · K ≠ Y`; half friction
      does not kill the gain; positive separations do not give zero
      unemployment; and `H_max` itself does not saturate the Pareto CDF.
    * S — lowering the saturation horizon does not keep the exposures
      ordered, and with `gK < 0` the sign of S3's response flips.
    * C — one month below the saturation horizon is not saturation, at equal
      horizons C4's strict ratio bound breaks, and half-automation does not
      give zero labor share.
    * B — the `Scenario` type admits the two horizons swapped, which is the
      constraint B2 exists to transport, and the fast bridge is not the
      baseline scenario.

  TIER: PIN. Nothing here is a falsification-surface point in its own right:
  the falsifiable claims live in `Calibration.lean`, and this file's value is
  that they are now consumed by the build. No stubbed proof term, no
  user axiom, no
  `decide` and no `native_decide` (CLAUDE.md hard rule 6: real-valued goals
  get `norm_num`), and no statement in `Calibration.lean` was edited to write
  it.
-/
import Economy.Calibration
import Economy.Empirical
import Mathlib.Tactic

namespace Economy

open Real Filter Topology

noncomputable section

/-! ### Part 1 — Witnesses at the cited data

The structures the validations quantify over, given here at the literals the
anchors name, so the legs below apply the corpus theorems to data rather than
to variables. -/

/-- The Acemoglu low corner `(exposure, costSavings, friction) = (0.20,
    0.033, 0)` as a point of `TFPParams`. `Bounds.acemoglu_low_corner` and
    `Calibration.validation_acemoglu_low` both carry this corner only as
    HYPOTHESES — unlike the Goldman corner there is no named def for it
    anywhere in the corpus — so this is where V1's literals stop being bound
    variables. -/
def acemogluLowBox : TFPParams where
  exposure := 20 / 100
  costSavings := 33 / 1000
  friction := 0
  exposure_nonneg := by norm_num
  exposure_le_one := by norm_num
  cost_nonneg := by norm_num
  cost_le_one := by norm_num
  fric_nonneg := by norm_num
  fric_le_one := by norm_num

/-- The S&P cost structure at V4's ceiling: labor share exactly 55% of
    revenue, capital plus tax exactly 319/1000 of revenue, so profit is
    exactly the cited 13.1% margin. -/
def spFirmAtCeiling : FirmCashFlow where
  revenue := 1000
  laborCost := 550
  capitalCost := 200
  tax := 119
  revenue_pos := by norm_num
  labor_nn := by norm_num
  capital_nn := by norm_num
  tax_nn := by norm_num

/-- The same firm with labor one point of revenue over V4's ceiling. -/
def spFirmLaborSlips : FirmCashFlow where
  revenue := 1000
  laborCost := 560
  capitalCost := 200
  tax := 119
  revenue_pos := by norm_num
  labor_nn := by norm_num
  capital_nn := by norm_num
  tax_nn := by norm_num

/-- The frictionless limit E4 names: Goldman's exposure and cost
    coefficients with `friction = 1`. -/
def tfpFullFriction : TFPParams where
  exposure := 40 / 100
  costSavings := 175 / 1000
  friction := 1
  exposure_nonneg := by norm_num
  exposure_le_one := by norm_num
  cost_nonneg := by norm_num
  cost_le_one := by norm_num
  fric_nonneg := by norm_num
  fric_le_one := by norm_num

/-- Half friction at the same exposure and cost coefficients: E4's hypothesis
    fails here, and so does its conclusion. -/
def tfpHalfFriction : TFPParams where
  exposure := 40 / 100
  costSavings := 175 / 1000
  friction := 1 / 2
  exposure_nonneg := by norm_num
  exposure_le_one := by norm_num
  cost_nonneg := by norm_num
  cost_le_one := by norm_num
  fric_nonneg := by norm_num
  fric_le_one := by norm_num

/-- The zero-labor factor-income point at the BEA labor share. With `L = 0`
    the labor FOC `w L = α Y` forces `Y = 0` at α = 0.60, and E2's content is
    that `r · K = Y` still holds on that corner. -/
def zeroLaborAtBEA : FactorIncome where
  Y := 0
  w := 1 / 2
  r := 3 / 1000
  L := 0
  K := 0
  α := 6 / 10
  foc_labor := by norm_num
  foc_capital := by norm_num

/-- The zero-capital factor-income point at full labor share: `K = 0` with
    output paid entirely to labor, so E3's `w · L = Y` is a live equality. -/
def zeroCapitalAllLabor : FactorIncome where
  Y := 1
  w := 1
  r := 3 / 1000
  L := 1
  K := 0
  α := 1
  foc_labor := by norm_num
  foc_capital := by norm_num

/-- An interior factor-income point: both FOCs hold, both factors are
    positive, so `r · K` is the capital share alone and cannot equal `Y`. -/
def interiorFactorIncome : FactorIncome where
  Y := 1
  w := 1 / 2
  r := 1 / 4
  L := 1
  K := 2
  α := 1 / 2
  foc_labor := by norm_num
  foc_capital := by norm_num

/-- The pessimistic twin of `Inequality.twoClassBEA`, reading its top-decile
    capital ownership out of `calPessimistic` so the range proofs come from
    the calibration subtype instead of a fresh numeral check. -/
noncomputable def twoClassPessimistic : TwoClass where
  α := 4 / 10
  ψ_k := calPessimistic.ψ_k.val
  ν_k := 1 / 10
  Y := 1
  α_nn := by norm_num
  α_le_one := by norm_num
  ψ_nn := calPessimistic.ψ_k.property.1.le
  ψ_le_one := calPessimistic.ψ_k.property.2.le
  ν_nn := by norm_num
  ν_le_one := by norm_num
  Y_pos := by norm_num

/-- A hand-written scenario carrying the two horizons swapped: legal as far
    as the `Scenario` type is concerned (both are positive), which is exactly
    why B2 has something to transport. -/
noncomputable def swappedHorizonScenario : Scenario where
  T := 4
  H₀ := 12
  Hmax := 1
  α := 6 / 10
  gK := 3 / 1000
  costSavings := 175 / 1000
  T_pos := by norm_num
  H₀_pos := by norm_num
  Hmax_pos := by norm_num
  α_pos := by norm_num
  α_lt_one := by norm_num
  gK_nn := by norm_num
  cost_nn := by norm_num

/-! ### Part 2 — V1–V6 consumed at the anchors -/

/-- **P-V1.** V1 applied at the Acemoglu corner: ΔTFP there is at most the
    cited 66/10000. Reddens if V1's bound literal, one of its three corner
    hypothesis literals, or the corner point above moves. -/
theorem pin_v1_acemoglu_low_at_corner : deltaTFP acemogluLowBox ≤ 66 / 10000 :=
  validation_acemoglu_low acemogluLowBox rfl rfl rfl

/-- **P-V1 anchor.** V1's conclusion read against the named literature anchor
    `Empirical.acemoglu_tfp_10yr` itself: the bound is taken from `Empirical`'s
    field rather than retyped here, so the leg reddens if either the validation
    or the cited estimate moves. -/
theorem pin_v1_anchor_agreement : deltaTFP acemogluLowBox ≤ acemoglu_tfp_10yr.value :=
  (validation_acemoglu_low acemogluLowBox rfl rfl rfl).trans (le_of_eq rfl)

/-- **P-V2.** V2 applied at the corpus's OWN named Goldman corner
    (`Productivity.tfpGoldmanCorner`): the three `rfl` hypothesis proofs only
    check while that def still reads exposure 0.40, costSavings 0.175 and
    friction 0. This is the tightest coupling in the file — an edit inside
    `Productivity.lean` reddens a leg standing in this one. -/
theorem pin_v2_goldman_high_at_corner : deltaTFP tfpGoldmanCorner ≤ 700 / 10000 :=
  validation_goldman_high tfpGoldmanCorner rfl rfl rfl

/-- **P-V2 anchor.** V2's conclusion read against the named Goldman anchor
    `goldman_gdp_10yr`, coupled the same way as P-V1: the envelope V2 proves is
    the envelope `Empirical` cites. -/
theorem pin_v2_anchor_agreement : deltaTFP tfpGoldmanCorner ≤ goldman_gdp_10yr.value := by
  refine (validation_goldman_high tfpGoldmanCorner rfl rfl rfl).trans ?_
  show (700 : ℝ) / 10000 ≤ (7 : ℝ) / 100
  norm_num

/-- **P-V3 evaluation.** The Mortensen–Pissarides formula at V3's own witness
    pair `(s, f) = (6/100, 94/100)` does reach the 6% magnitude. Reddens if
    `MatchingModel.steadyStateU` is redefined or V3's threshold moves. -/
theorem pin_v3_at_witness_pair : steadyStateU (6 / 100) (94 / 100) ≥ 6 / 100 := by
  unfold steadyStateU
  norm_num

/-- **P-V3 consumed.** V3's witness rescales to a genuine pair of RATES in
    `[0, 1]` — a strengthening V3 does not state, since its `s` and `f` are
    unconstrained magnitudes chosen to hit the anchor. The pair comes only
    from V3's existential. -/
theorem pin_v3_witness_rescales_to_rates :
    ∃ s f : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ 0 < f ∧ f ≤ 1 ∧ steadyStateU s f ≥ 6 / 100 := by
  obtain ⟨s, f, hs, hf, hle⟩ := validation_brynjolfsson
  have hsum : 0 < s + f := by linarith
  have hkey : steadyStateU (s / (s + f)) (f / (s + f)) = steadyStateU s f := by
    unfold steadyStateU
    field_simp
  refine ⟨s / (s + f), f / (s + f), div_nonneg hs hsum.le, ?_,
    div_pos hf hsum, ?_, ?_⟩
  · exact (div_le_iff₀ hsum).mpr (by linarith)
  · exact (div_le_iff₀ hsum).mpr (by linarith)
  · rw [hkey]
    exact hle

/-- **P-V3 anchor.** V3's witness pair read against the magnitude of the BCC
    anchor `brynjolfsson2025_young`: the corpus states that effect as a −6%
    employment change, and the unemployment side of the same number is the
    magnitude V3 reaches. Reddens if V3's threshold or the anchor moves. -/
theorem pin_v3_anchor_agreement :
    ∃ s f : ℝ, 0 ≤ s ∧ 0 < f ∧ steadyStateU s f ≥ -brynjolfsson2025_young.value := by
  obtain ⟨s, f, hs, hf, hle⟩ := validation_brynjolfsson
  have h6 : (6 : ℝ) / 100 = -brynjolfsson2025_young.value := by
    show (6 : ℝ) / 100 = -((-6 : ℝ) / 100)
    norm_num
  rw [← h6]
  exact ⟨s, f, hs, hf, hle⟩

/-- **P-V4.** V4 applied at the S&P cost structure: at exactly the 55% labor
    ceiling and 319/1000 capital-plus-tax, the margin is the cited 13.1%. -/
theorem pin_v4_sp_margin_at_ceiling : spFirmAtCeiling.margin ≥ 131 / 1000 := by
  refine validation_sp_margin spFirmAtCeiling ?_ ?_
  · show (550 : ℝ) / 1000 ≤ 55 / 100
    norm_num
  · show ((200 : ℝ) + 119) / 1000 ≤ 319 / 1000
    norm_num

/-- **Negative control, validation family.** Goldman's corner does NOT
    satisfy Acemoglu's bound. Proved through the corpus's own evaluation of
    the Hulten formula at that corner, `deltaTFP_tfpGoldmanCorner`, so it says
    the model output actually moves with the anchors instead of being a
    constant any bound swallows. -/
theorem neg_v1_acemoglu_bound_fails_at_goldman_corner :
    ¬ (deltaTFP tfpGoldmanCorner ≤ 66 / 10000) := by
  rw [deltaTFP_tfpGoldmanCorner]
  norm_num

/-- **Negative control, validation family.** One point of revenue of extra
    labor cost puts the firm under the cited margin: V4's labor ceiling is
    doing the work, not slack in its arithmetic. Proved from `margin` and
    `profit` as `FinancialMarkets` defines them. -/
theorem neg_v4_labor_slip_breaks_margin : ¬ (spFirmLaborSlips.margin ≥ 131 / 1000) := by
  show ¬ ((1000 : ℝ) - 560 - 200 - 119) / 1000 ≥ 131 / 1000
  norm_num

/-- **P-V5.** The hyperscaler capex pin evaluated at two different
    calibrations, restated at the MUFG literal 22/1000. The function ignores
    its argument, so the second leg is `rfl` — which is exactly the content
    V5's own docstring labels a NUMERICAL OBSERVATION. -/
theorem pin_v5_hyperscaler_share_at_calibrations :
    hyperscalerCapexShare calBEA2026 = 22 / 1000 ∧
      hyperscalerCapexShare calPessimistic = 22 / 1000 :=
  ⟨validation_hyperscaler_share, rfl⟩

/-- **P-V6.** V6 restated independently at the 24-month METR horizon and the
    `calBEA2026` doubling time: 24 and 64 are now written in two files. -/
theorem pin_v6_metr_24mo_at_calibration :
    intelligenceLevel 24 calBEA2026.doublingTime = 64 :=
  validation_metr_24mo

/-- **P-doubling.** The three canonical calibrations carry the three METR
    doubling times the corpus cites: fast 4, baseline 7, pessimistic 4 months.
    Reddens if a `β_slope` field is edited or a slope def moves. -/
theorem pin_doubling_times_at_calibrations :
    calBEA2026.doublingTime = 4 ∧ calBaseline.doublingTime = 7 ∧
      calPessimistic.doublingTime = 4 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold ModelCalibration.doublingTime calBEA2026
    exact doublingTime_metrFast
  · unfold ModelCalibration.doublingTime calBaseline
    exact doublingTime_metrBaseline
  · unfold ModelCalibration.doublingTime calPessimistic
    exact doublingTime_metrFast

/-- **P-doubling positivity.** `doublingTime_pos` evaluated at all three
    calibrations — the field the scenario bridge needs to build a `Scenario`. -/
theorem pin_doublingTime_pos_at_calibrations :
    0 < calBEA2026.doublingTime ∧ 0 < calBaseline.doublingTime ∧
      0 < calPessimistic.doublingTime :=
  ⟨ModelCalibration.doublingTime_pos calBEA2026,
   ModelCalibration.doublingTime_pos calBaseline,
   ModelCalibration.doublingTime_pos calPessimistic⟩

/-! ### Part 3 — E1–E7 consumed at the boundary points -/

/-- **P-E1.** The slow-growth limit at the METR 24-month horizon: as the
    doubling time diverges, capability 24 months out tends to the initial
    level. -/
theorem pin_e1_intelligence_limit_at_24mo :
    Tendsto (fun T : ℝ => intelligenceLevel 24 T) atTop (𝓝 1) :=
  edge_intelligence_tendsto_one 24

/-- **P-E2.** E2 at the BEA labor share with zero hours: `r · K = Y` on the
    `L = 0` corner. -/
theorem pin_e2_zero_labor_at_BEA_alpha :
    zeroLaborAtBEA.r * zeroLaborAtBEA.K = zeroLaborAtBEA.Y :=
  edge_zero_labor zeroLaborAtBEA rfl

/-- **P-E3.** E3 with capital removed and output paid entirely to labor. -/
theorem pin_e3_zero_capital_at_full_labor_share :
    zeroCapitalAllLabor.w * zeroCapitalAllLabor.L = zeroCapitalAllLabor.Y :=
  edge_zero_capital zeroCapitalAllLabor rfl

/-- **P-E4.** E4 at full friction with live exposure and cost coefficients. -/
theorem pin_e4_perfect_friction_kills_gain : deltaTFP tfpFullFriction = 0 :=
  edge_perfect_friction tfpFullFriction rfl

/-- **P-E5.** The Pareto exposure CDF tends to saturation as the task horizon
    diverges, at shape index α = 1 and the base horizon of `calBEA2026`. -/
theorem pin_e5_pareto_tends_to_one_at_BEA :
    Tendsto (paretoCDF 1 calBEA2026.H_min.val) atTop (𝓝 1) :=
  edge_infinite_horizon (by norm_num : (0 : ℝ) < 1) calBEA2026.H_min.property

/-- **P-E6.** Zero separations give zero unemployment at the BCC finding rate
    94/100. -/
theorem pin_e6_zero_separations_at_BCC_finding_rate :
    steadyStateU 0 (94 / 100) = 0 :=
  edge_zero_separations (by norm_num : (0 : ℝ) < 94 / 100)

/-- **P-E7.** Arbitrarily fast matching annihilates unemployment at the BCC
    separation rate 6/100. -/
theorem pin_e7_matching_limit_at_BCC_separation_rate :
    Tendsto (fun f : ℝ => steadyStateU (6 / 100) f) atTop (𝓝 0) :=
  edge_infinite_matching (6 / 100) (by norm_num : (0 : ℝ) ≤ 6 / 100)

/-- **P-E5 value.** At the calibration's own saturation horizon the Pareto CDF
    is 11/12: `H_min = 1` and `H_max = 12` are read through `calBEA2026`'s
    fields, so editing either horizon reddens this leg. -/
theorem pin_e5_pareto_value_at_BEA_horizon :
    paretoCDF 1 calBEA2026.H_min.val calBEA2026.H_max.val = 11 / 12 := by
  show (if (12 : ℝ) ≤ 1 then (0 : ℝ) else 1 - ((1 : ℝ) / 12) ^ (1 : ℝ)) = 11 / 12
  split_ifs with h
  · exact absurd h (show ¬ ((12 : ℝ) ≤ 1) from by norm_num)
  · rw [Real.rpow_one]
    norm_num

/-- **Negative control, edge family (E5).** The saturation horizon does NOT
    saturate the Pareto CDF: the limit E5 states is a limit, not a value. -/
theorem neg_e5_saturation_horizon_is_not_saturated :
    paretoCDF 1 calBEA2026.H_min.val calBEA2026.H_max.val ≠ 1 := by
  rw [pin_e5_pareto_value_at_BEA_horizon]
  norm_num

/-- **Negative control, edge family (E6).** Positive separations do NOT give
    zero unemployment, at the same finding rate E6 is evaluated at. -/
theorem neg_e6_positive_separations_are_not_zero_unemployment :
    steadyStateU (6 / 100) (94 / 100) ≠ 0 := by
  unfold steadyStateU
  norm_num

/-- **Negative control, edge family (E2/E3).** An interior factor-income
    point — both factors paid, both FOCs satisfied — has `r · K ≠ Y`. That is
    E2's boundary predicate denied for a literal with `L ≠ 0`; without it E2
    would say nothing about where the degeneracy bites. -/
theorem neg_e2_interior_point_breaks_zero_labor_identity :
    ¬ (interiorFactorIncome.r * interiorFactorIncome.K = interiorFactorIncome.Y) := by
  show ¬ ((1 : ℝ) / 4 * 2 = 1)
  norm_num

/-- **Negative control, edge family (E4).** Half friction does NOT kill the
    gain at the same exposure and cost coefficients. -/
theorem neg_e4_half_friction_does_not_kill_gain : deltaTFP tfpHalfFriction ≠ 0 := by
  show (40 / 100 : ℝ) * (175 / 1000) * (1 - 1 / 2) ≠ 0
  norm_num

/-! ### Part 4 — S1–S5 consumed at the calibration data -/

/-- **P-S1.** S1 evaluated at the three forecast horizons the blog cites
    (0, 12 and 24 months): the baseline scenario never overtakes the fast one
    at `t ≥ 0`. -/
theorem pin_s1_at_forecast_horizons :
    metrBaselineScenario.logGDPDeviation 0 ≤ metrFastScenario.logGDPDeviation 0 ∧
      metrBaselineScenario.logGDPDeviation 12 ≤ metrFastScenario.logGDPDeviation 12 ∧
      metrBaselineScenario.logGDPDeviation 24 ≤ metrFastScenario.logGDPDeviation 24 := by
  refine ⟨gdp_mono_in_β_slope (le_refl 0), gdp_mono_in_β_slope ?_,
    gdp_mono_in_β_slope ?_⟩ <;> norm_num

/-- **P-S1 at the calibration layer.** The bridge-built baseline calibration
    stays below the bridge-built fast calibration at 24 months. -/
theorem pin_s1_at_calibrations_24mo :
    (Scenario.fromCalibration calBaseline).logGDPDeviation 24 ≤
      (Scenario.fromCalibration calBEA2026).logGDPDeviation 24 :=
  gdp_mono_in_β_slope_at_calibrations (by norm_num : (0 : ℝ) ≤ 24)

/-- **P-S2.** Raising the saturation horizon from `calBEA2026`'s 12 months to
    24 weakly lowers the exposure of a 6-month task. -/
theorem pin_s2_raising_Hmax_lowers_exposure :
    exposureFromHorizon 6 24 ≤ exposureFromHorizon 6 calBEA2026.H_max.val := by
  refine gdp_antitone_in_H_max calBEA2026.H_max.property ?_ ?_ ?_
  · norm_num
  · show (12 : ℝ) ≤ 24
    norm_num
  · norm_num

/-- **P-S3.** Lowering the labor share from the BEA calibration's α to the
    pessimistic calibration's, at the BEA capex rate, weakly raises the
    Ghost-GDP growth rate. Both α literals are read through the calibrations. -/
theorem pin_s3_lowering_alpha_raises_ghost_gdp :
    (0 : ℝ) + (1 - calBEA2026.α.val) * calBEA2026.gK.val ≤
      (0 : ℝ) + (1 - calPessimistic.α.val) * calBEA2026.gK.val :=
  gdp_mono_in_α calBEA2026.gK.property
    (show (55 : ℝ) / 100 ≤ 6 / 10 from by norm_num)

/-- **P-S4.** The BEA carrier's top-decile share is at most the pessimistic
    carrier's, whose ownership field IS `calPessimistic`'s ψ_k. -/
theorem pin_s4_at_carriers :
    twoClassBEA.topDecileShare ≤ twoClassPessimistic.topDecileShare :=
  welfare_antitone_in_ψ_k twoClassBEA twoClassPessimistic rfl rfl rfl
    (show (77 : ℝ) / 100 ≤ 85 / 100 from by norm_num)

/-- **P-S5.** A higher MPC at the same `τ = 0` gives a strictly larger
    Keynesian response, read at `calBEA2026`'s and `calPessimistic`'s own m
    fields. -/
theorem pin_s5_mpc_response_at_calibrations :
    (1 : ℝ) * (1 / (1 - calBEA2026.m.val * (1 - 0))) <
      (1 : ℝ) * (1 / (1 - calPessimistic.m.val * (1 - 0))) := by
  refine consumption_mono_in_m ?_ ?_ ?_ ?_ ?_ ?_
  · exact calBEA2026.m.property.1
  · show (9 : ℝ) / 10 < 95 / 100
    norm_num
  · exact calPessimistic.m.property.2
  · exact le_refl 0
  · norm_num
  · norm_num

/-- **Negative control, sensitivity family (S2).** Lowering the saturation
    horizon does NOT keep the large-horizon exposure below the small one. -/
theorem neg_s2_lowering_Hmax_raises_exposure :
    ¬ (exposureFromHorizon 6 calBEA2026.H_max.val ≤ exposureFromHorizon 6 24) := by
  have h12 : exposureFromHorizon (6 : ℝ) calBEA2026.H_max.val = 1 / 2 := by
    show min 1 (max 0 ((6 : ℝ) / 12)) = 1 / 2
    rw [max_eq_right (show (0 : ℝ) ≤ 6 / 12 from by norm_num),
      min_eq_right (show (6 : ℝ) / 12 ≤ 1 from by norm_num)]
    norm_num
  have h24 : exposureFromHorizon (6 : ℝ) 24 = 1 / 4 := by
    show min 1 (max 0 ((6 : ℝ) / 24)) = 1 / 4
    rw [max_eq_right (show (0 : ℝ) ≤ 6 / 24 from by norm_num),
      min_eq_right (show (6 : ℝ) / 24 ≤ 1 from by norm_num)]
    norm_num
  rw [h12, h24]
  norm_num

/-- **Negative control, sensitivity family (S3).** The monotonicity is
    conditional on nonnegative capital growth: at `gK = -1` the order flips,
    which is why S3 states the hypothesis instead of a bare inequality. -/
theorem neg_s3_negative_capital_growth_reverses_order :
    ¬ ((0 : ℝ) + (1 - calBEA2026.α.val) * (-1) ≤
      (0 : ℝ) + (1 - calPessimistic.α.val) * (-1)) := by
  show ¬ ((0 : ℝ) + (1 - 6 / 10) * (-1) ≤ 0 + (1 - 55 / 100) * (-1))
  norm_num

/-! ### Part 5 — C1–C4 consumed at the calibrations -/

/-- **P-C1.** Exposure at the saturation horizon is exactly 1 for all three
    canonical calibrations. -/
theorem pin_c1_saturation_at_calibrations :
    exposureFromHorizon calBEA2026.H_max.val calBEA2026.H_max.val = 1 ∧
      exposureFromHorizon calBaseline.H_max.val calBaseline.H_max.val = 1 ∧
      exposureFromHorizon calPessimistic.H_max.val calPessimistic.H_max.val = 1 :=
  ⟨exposure_consistency calBEA2026, exposure_consistency calBaseline,
   exposure_consistency calPessimistic⟩

/-- **P-C4.** C4 evaluated at the BEA calibration and restated independently:
    the clipping is inactive below saturation and the ratio is strictly
    inside `(0, 1)`. -/
theorem pin_c4_at_BEA :
    exposureFromHorizon calBEA2026.H_min.val calBEA2026.H_max.val =
        calBEA2026.H_min.val / calBEA2026.H_max.val ∧
      0 < calBEA2026.H_min.val / calBEA2026.H_max.val ∧
      calBEA2026.H_min.val / calBEA2026.H_max.val < 1 :=
  exposure_below_saturation calBEA2026

/-- **P-C4 ratio.** The identity half of C4 at all three calibrations, with
    the ratio written at the cited numbers: 1/12 everywhere. This is what
    pins `H_min = 1, H_max = 12` in all three, not just in the one C4b reads. -/
theorem pin_c4_ratio_at_calibrations :
    exposureFromHorizon calBEA2026.H_min.val calBEA2026.H_max.val = 1 / 12 ∧
      exposureFromHorizon calBaseline.H_min.val calBaseline.H_max.val = 1 / 12 ∧
      exposureFromHorizon calPessimistic.H_min.val calPessimistic.H_max.val = 1 / 12 :=
  ⟨(exposure_below_saturation calBEA2026).1.trans rfl,
   (exposure_below_saturation calBaseline).1.trans rfl,
   (exposure_below_saturation calPessimistic).1.trans rfl⟩

/-- **P-C4b.** The published numerical observation restated at its own
    literals in a second file. -/
theorem pin_c4b_base_exposure_is_one_twelfth :
    exposureFromHorizon calBEA2026.H_min.val calBEA2026.H_max.val = 1 / 12 :=
  calBEA2026_exposure_at_base

/-- **P-C2.** Labor-share consistency at three weighted tasks under full
    automation. -/
theorem pin_c2_full_automation_three_tasks :
    laborShare (fun _ : Fin 3 => (6 : ℝ) / 10) (fun _ => (1 : ℝ)) = 0 :=
  labor_share_consistency _

/-- **P-C3.** The welfare-can-fall witness seen from the calibration layer,
    stated independently at `calBEA2026`. -/
theorem pin_c3_at_BEA :
    ∃ Y Y' lam lam' : ℝ, 0 < Y ∧ 0 < Y' ∧ 0 < lam ∧ 0 < lam' ∧ Y < Y' ∧
      welfareDelta (lam * Y) (lam' * Y') < 0 :=
  welfare_consistency calBEA2026

/-- **Negative control, consistency family (C1).** One month below the
    saturation horizon is NOT saturation: C1's `= 1` holds exactly at
    `H = H_max`, which is what makes it a boundary pin rather than a clip. -/
theorem neg_c1_one_month_below_is_not_saturated :
    exposureFromHorizon 11 calBEA2026.H_max.val ≠ 1 := by
  show min 1 (max 0 ((11 : ℝ) / 12)) ≠ 1
  rw [max_eq_right (show (0 : ℝ) ≤ 11 / 12 from by norm_num),
    min_eq_right (show (11 : ℝ) / 12 ≤ 1 from by norm_num)]
  norm_num

/-- **Negative control, consistency family (C4).** At equal horizons the
    strict ratio bound C4 claims for `H_min / H_max` is false: the literal
    that shows `H_min_lt_H_max` does work and is not inert decoration. -/
theorem neg_c4_equal_horizons_break_strictness :
    ¬ (calBEA2026.H_max.val / calBEA2026.H_max.val < 1) := by
  show ¬ ((12 : ℝ) / 12 < 1)
  norm_num


/-- **Negative control, consistency family (C2).** Half-automation with a
    positive weight does not give zero labor share. -/
theorem neg_c2_partial_automation_is_not_zero_share :
    ¬ (laborShare (fun _ : Fin 1 => (6 : ℝ) / 10) (fun _ => (1 : ℝ) / 2) = 0) := by
  intro h
  have hsum : laborShare (fun _ : Fin 1 => (6 : ℝ) / 10) (fun _ => (1 : ℝ) / 2)
      = (6 / 10) * (1 - 1 / 2) := by
    unfold laborShare
    exact Fin.sum_univ_one _
  rw [hsum] at h
  norm_num at h

/-! ### Part 6 — the scenario bridge consumed -/

/-- **P-B1.** The bridge's six data legs at `calBEA2026`, restated
    independently: a reordered field, a swapped horizon or a defaulted
    cost-savings reddens this leg. -/
theorem pin_b1_at_BEA :
    (Scenario.fromCalibration calBEA2026).T = calBEA2026.doublingTime ∧
      (Scenario.fromCalibration calBEA2026).H₀ = calBEA2026.H_min.val ∧
      (Scenario.fromCalibration calBEA2026).Hmax = calBEA2026.H_max.val ∧
      (Scenario.fromCalibration calBEA2026).α = calBEA2026.α.val ∧
      (Scenario.fromCalibration calBEA2026).gK = calBEA2026.gK.val ∧
      (Scenario.fromCalibration calBEA2026).costSavings = calBEA2026.costSavings.val :=
  fromCalibration_data_legs calBEA2026

/-- **P-B1 cross-layer.** The bridge-built scenario carries the forecast
    layer's OWN `metrFastScenario` numbers on the five fields B3 does not have
    to argue about. Consumes B3, so it reddens if either copy moves. -/
theorem pin_b1_bridge_carries_forecast_literals :
    (Scenario.fromCalibration calBEA2026).H₀ = metrFastScenario.H₀ ∧
      (Scenario.fromCalibration calBEA2026).Hmax = metrFastScenario.Hmax ∧
      (Scenario.fromCalibration calBEA2026).α = metrFastScenario.α ∧
      (Scenario.fromCalibration calBEA2026).gK = metrFastScenario.gK ∧
      (Scenario.fromCalibration calBEA2026).costSavings = metrFastScenario.costSavings := by
  rw [fromCalibration_calBEA2026_matches_metrFastScenario]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **P-B2.** The horizon ordering survives the bridge at `calBEA2026`. -/
theorem pin_b2_ordering_survives_bridge :
    (Scenario.fromCalibration calBEA2026).H₀ < (Scenario.fromCalibration calBEA2026).Hmax :=
  fromCalibration_Hmin_lt_Hmax calBEA2026

/-- **P-B3.** The fast bridge reproduces `Economy.Forecast`'s own fast
    scenario, restated in this file. -/
theorem pin_b3_fast_bridge_matches_forecast :
    Scenario.fromCalibration calBEA2026 = metrFastScenario :=
  fromCalibration_calBEA2026_matches_metrFastScenario

/-- **P-B4.** The baseline side of the same pin. -/
theorem pin_b4_baseline_bridge_matches_forecast :
    Scenario.fromCalibration calBaseline = metrBaselineScenario :=
  fromCalibration_calBaseline_matches_metrBaselineScenario

/-- **Negative control, bridge family (B2).** The `Scenario` type admits the
    two horizons swapped — positive base horizon, positive saturation horizon,
    ordering violated. That is the constraint B2 transports and a hand-written
    scenario can silently lose. -/
theorem neg_b2_scenario_type_admits_swapped_horizons :
    ¬ (swappedHorizonScenario.H₀ < swappedHorizonScenario.Hmax) := by
  show ¬ ((12 : ℝ) < 1)
  norm_num

/-- **Negative control, bridge family (B3/B4).** The fast bridge is NOT the
    baseline scenario: they differ in doubling time, 4 against 7 — the one
    field B3 and B4 argue about, so the two pins are not interchangeable. -/
theorem neg_b3_fast_bridge_is_not_baseline_scenario :
    Scenario.fromCalibration calBEA2026 ≠ metrBaselineScenario := by
  intro h
  have hT : calBEA2026.doublingTime = 7 :=
    ((fromCalibration_data_legs calBEA2026).1.trans
      (congrArg Scenario.T h)).trans rfl
  linarith [pin_doubling_times_at_calibrations.1]

end

end Economy
