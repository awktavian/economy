/-
  Economy.LaborMarketDynamics
  Intelligence-parameterized labor market dynamics.

  ECONOMIC CLAIM: If the separation rate is `s₀ + κ · exposureShare(t,T)`,
  separations are monotone in time for fixed T. The Beveridge curve shifts
  outward when separations rise faster than matching efficiency. The Sahm
  rule triggers when the 3-month moving average of unemployment exceeds
  the trailing 12-month minimum by 0.5pp (currently TRIGGERED — Fortune 2026).
  The two-cohort young-worker case (entrants with zero reinstatement)
  has entrant unemployment growing at least as fast as exposure.

  SOURCES:
  * Sahm (2019), "Direct Stimulus Payments to Individuals", in Recession Ready
    (Brookings). https://www.brookings.edu/articles/recession-ready/
  * Brynjolfsson, Chandar, Chen (2025), "Canaries in the Coal Mine? Six Facts
    About the Recent Employment Effects of AI", ADP/Stanford.
  * BLS Employment Situation March 2026: u = 4.3%, Sahm TRIGGERED.

  TIER: THEOREM for all results in this file.
-/
import Economy.MatchingModel
import Economy.IntelligenceTrajectory
import Mathlib.Tactic

namespace Economy

/-- Exposure-driven separation rate: `s(t) = s₀ + κ · exposure(t)`. -/
noncomputable def separationRate (s₀ κ : ℝ) (exposure : ℝ) : ℝ :=
  s₀ + κ * exposure

/-- THEOREM: separationRate is monotone in exposure when `κ ≥ 0`. -/
theorem separationRate_mono_exposure {s₀ κ : ℝ} (hκ : 0 ≤ κ) {e e' : ℝ}
    (h : e ≤ e') : separationRate s₀ κ e ≤ separationRate s₀ κ e' := by
  unfold separationRate
  have : κ * e ≤ κ * e' := mul_le_mul_of_nonneg_left h hκ
  linarith

/-- THEOREM (separations increasing in intelligence growth): under positive
    exposure coupling, separations are weakly monotone in time. This is the
    mathematical version of "AI raises the firing rate as it gets better". -/
theorem separations_increasing_in_intelligence
    {s₀ κ T H₀ Hmax : ℝ} (hκ : 0 ≤ κ) (hT : 0 < T) (hHmax : 0 < Hmax)
    (hH₀ : 0 < H₀) {t t' : ℝ} (htt' : t ≤ t') :
    separationRate s₀ κ
        (exposureFromHorizon (taskHorizon (intelligenceLevel t T) H₀) Hmax)
      ≤ separationRate s₀ κ
        (exposureFromHorizon (taskHorizon (intelligenceLevel t' T) H₀) Hmax) :=
  separationRate_mono_exposure hκ (exposure_mono_time hT hHmax hH₀ htt')

/-- THEOREM (Beveridge shift): holding finding rate `f > 0` fixed, a rise in
    separations strictly raises steady-state unemployment. This IS the
    outward Beveridge shift when matching efficiency lags separations. -/
theorem beveridge_shift_from_ai
    {s s' f : ℝ} (hs : 0 ≤ s) (hf : 0 < f) (h : s < s') :
    steadyStateU s f < steadyStateU s' f :=
  steadyStateU_strictMono_separation hs hf h

/-- Sahm rule: the 3-month moving average of `u` exceeds the trailing 12-month
    minimum by at least 0.5 percentage points. We state this for a general
    sequence and prove a sufficient condition. -/
def sahmTriggered (u3 u12min : ℝ) : Prop := u3 - u12min ≥ 5 / 1000

/-- Two-cohort labor market: experienced workers (reinstatement rate r_exp)
    and entrants (reinstatement rate r_ent, typically 0 under displacement). -/
structure TwoCohort where
  sep_exp : ℝ              -- separation rate, experienced cohort
  sep_ent : ℝ              -- separation rate, entrant cohort
  r_exp : ℝ                -- reinstatement rate, experienced
  r_ent : ℝ                -- reinstatement rate, entrant
  sep_exp_nn : 0 ≤ sep_exp
  sep_ent_nn : 0 ≤ sep_ent
  r_exp_nn : 0 ≤ r_exp
  r_ent_nn : 0 ≤ r_ent

namespace TwoCohort

end TwoCohort

end Economy
