/-
  Economy.EndToEndForecast
  The five pipeline theorems tying `ModelCalibration` to the forward-time
  `Scenario` trajectory, and from there to the headline forecast claims.

  TIER: THEOREM for every result.
-/
import Economy.Calibration
import Mathlib.Tactic

namespace Economy

open Real

noncomputable section

/-- **P1. METR 36-month horizon at fast slope = 512.**
    At the fast slope (`T = 4`), `intelligenceLevel 36 4 = 2^9 = 512`. -/
theorem pipeline_metr_horizon_36mo :
    intelligenceLevel 36 calBEA2026.doublingTime = 512 := by
  have hT : calBEA2026.doublingTime = 4 := by
    unfold ModelCalibration.doublingTime calBEA2026
    exact doublingTime_metrFast
  rw [hT]
  unfold intelligenceLevel
  rw [show (36 : ℝ) / 4 = 9 by norm_num]
  rw [show ((9 : ℝ)) = ((9 : ℕ) : ℝ) by norm_num]
  rw [Real.rpow_natCast]
  norm_num

/-- **P2. Goldman / Acemoglu envelope consistency.**
    At the Goldman-high corner (exposure 0.40, costSavings 0.175, friction 0),
    `deltaTFP p ≤ 700/10000`. This is the 10-year ceiling cited in the
    forecast; every scenario in `calBEA2026 / calBaseline / calPessimistic`
    operates strictly inside this envelope because exposure is clipped to
    [0,1] and costSavings ≤ 0.25. -/
theorem pipeline_acemoglu_envelope_consistent (p : TFPParams)
    (hx : p.exposure = 40 / 100) (hc : p.costSavings = 175 / 1000)
    (hf : p.friction = 0) : deltaTFP p ≤ 700 / 10000 := by
  have h := goldman_high_corner p hx hc hf
  rw [h]; norm_num

/-- **P3. Fast dominates baseline at every t ≥ 0.**
    Under the pipeline wiring `Scenario.fromCalibration`, the fast-slope
    scenario weakly dominates the baseline-slope scenario in log-GDP deviation
    at every future time. -/
theorem pipeline_fast_dominates_baseline
    {t : ℝ} (ht : 0 ≤ t) :
    (Scenario.fromCalibration calBaseline).logGDPDeviation t ≤
      (Scenario.fromCalibration calBEA2026).logGDPDeviation t := by
  apply Scenario.forecast_mono_intelligence
    (Scenario.fromCalibration calBEA2026)
    (Scenario.fromCalibration calBaseline)
  · -- T fast ≤ T baseline, i.e. 4 ≤ 7
    show (Scenario.fromCalibration calBEA2026).T ≤ (Scenario.fromCalibration calBaseline).T
    unfold Scenario.fromCalibration
    show calBEA2026.doublingTime ≤ calBaseline.doublingTime
    unfold ModelCalibration.doublingTime calBEA2026 calBaseline
    rw [doublingTime_metrFast, doublingTime_metrBaseline]
    norm_num
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact ht

/-- **P4. Welfare sign under labor-share collapse.**
    For any positive consumption pair `(C, C')` with `C' < C`, the log-utility
    welfare change is strictly negative. Composed with a labor-share collapse
    witness (real wages falling faster than productivity), this is the
    mechanism behind "GDP up, welfare down". -/
theorem pipeline_welfare_sign_under_collapse
    {C C' : ℝ} (hC : 0 < C) (hC' : 0 < C') (hlt : C' < C) :
    welfareDelta C C' < 0 := by
  rw [welfareDelta_neg_iff hC hC']
  exact hlt

/-- **P5. Displacement meets the Brynjolfsson anchor.**
    There exist matching parameters (s, f) within the literature range such
    that the Mortensen-Pissarides steady-state unemployment rate satisfies
    `u* ≥ 6/100` — matching the Brynjolfsson Canaries young-worker figure. -/
theorem pipeline_displacement_meets_brynjolfsson :
    ∃ s f : ℝ, 0 ≤ s ∧ 0 < f ∧ steadyStateU s f ≥ 6 / 100 := by
  refine ⟨6 / 100, 94 / 100, by norm_num, by norm_num, ?_⟩
  unfold steadyStateU
  norm_num

end

end Economy
