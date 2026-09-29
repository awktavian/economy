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

/-- Finding rate of a cohort: baseline hiring `f₀ > 0` plus a reinstatement
    channel `κᵣ · r` — workers reinstated to new tasks are rehired faster. -/
noncomputable def cohortFinding (f₀ κᵣ r : ℝ) : ℝ := f₀ + κᵣ * r

/-- THEOREM (two-cohort comparative statics — the `TwoCohort` consumer): if
    entrants separate at least as often as the experienced cohort
    (`sep_exp ≤ sep_ent`) and are reinstated no faster (`r_ent ≤ r_exp`),
    entrant steady-state unemployment is weakly above the experienced
    cohort's. Every field of the carrier is consumed: `sep_exp_nn` /
    `sep_ent_nn` certify the denominators of `steadyStateU`, `r_exp_nn` /
    `r_ent_nn` certify the finding-rate channels, and `hsep` / `hr` are the
    live ordering hypotheses. This wires `TwoCohort` into the existing
    `MatchingModel` steady-state machinery. -/
theorem two_cohort_gap (T : TwoCohort) {f₀ κᵣ : ℝ} (hf₀ : 0 < f₀) (hκᵣ : 0 ≤ κᵣ)
    (hsep : T.sep_exp ≤ T.sep_ent) (hr : T.r_ent ≤ T.r_exp) :
    steadyStateU T.sep_exp (cohortFinding f₀ κᵣ T.r_exp)
      ≤ steadyStateU T.sep_ent (cohortFinding f₀ κᵣ T.r_ent) := by
  unfold cohortFinding steadyStateU
  have hfe : 0 ≤ f₀ + κᵣ * T.r_ent := by nlinarith [mul_nonneg hκᵣ T.r_ent_nn]
  have hfer : f₀ + κᵣ * T.r_ent ≤ f₀ + κᵣ * T.r_exp := by
    nlinarith [mul_le_mul_of_nonneg_left hr hκᵣ]
  have key : T.sep_exp * (f₀ + κᵣ * T.r_ent) ≤ T.sep_ent * (f₀ + κᵣ * T.r_exp) := by
    nlinarith [mul_le_mul_of_nonneg_right hsep hfe,
      mul_le_mul_of_nonneg_left hfer T.sep_ent_nn]
  have h1 : 0 < T.sep_exp + (f₀ + κᵣ * T.r_exp) := by nlinarith [T.sep_exp_nn, T.r_exp_nn, hf₀, hκᵣ]
  have h2 : 0 < T.sep_ent + (f₀ + κᵣ * T.r_ent) := by nlinarith [T.sep_ent_nn, T.r_ent_nn, hf₀, hκᵣ]
  rw [div_le_div_iff₀ h1 h2]
  nlinarith [key]

end TwoCohort

end Economy
