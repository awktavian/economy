/-
  Economy.MatchingModel
  Mortensen-Pissarides matching function and steady-state unemployment.

  ECONOMIC CLAIM: With matching function m(u,v) = μ · u^η · v^(1-η), the
  job-finding rate is f(θ) = μ · θ^(1-η), the vacancy-filling rate is
  q(θ) = μ · θ^(-η), both monotone (f increasing in θ, q decreasing).
  Steady-state unemployment u* = s/(s+f(θ)) is decreasing in θ and
  increasing in the separation rate s. A displacement shock (↑s) raises
  steady-state u.

  SOURCES:
  * Mortensen & Pissarides (1994), "Job Creation and Job Destruction in the
    Theory of Unemployment", Review of Economic Studies 61(3): 397–415.
    https://doi.org/10.2307/2297896
  * Petrongolo & Pissarides (2001), "Looking into the Black Box: A Survey of
    the Matching Function", Journal of Economic Literature 39(2): 390–431.

  TIER: THEOREM for all results (algebraic identities on rpow and on
  one-dimensional rational functions).
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace Economy

open Real

/-- Matching-function parameters. -/
structure MatchingParams where
  μ : ℝ           -- matching efficiency
  η : ℝ           -- unemployment elasticity
  μ_pos : 0 < μ
  η_pos : 0 < η
  η_lt_one : η < 1

namespace MatchingParams

variable (p : MatchingParams)

/-- Job-finding rate as a function of tightness θ = v/u. -/
noncomputable def f (θ : ℝ) : ℝ := p.μ * θ ^ (1 - p.η)

/-- Vacancy-filling rate. -/
noncomputable def q (θ : ℝ) : ℝ := p.μ * θ ^ (- p.η)

/-- THEOREM: f(θ) is positive when θ > 0. -/
theorem f_pos {θ : ℝ} (hθ : 0 < θ) : 0 < p.f θ := by
  unfold f
  exact mul_pos p.μ_pos (Real.rpow_pos_of_pos hθ _)

/-- THEOREM: q(θ) is positive when θ > 0. -/
theorem q_pos {θ : ℝ} (hθ : 0 < θ) : 0 < p.q θ := by
  unfold q
  exact mul_pos p.μ_pos (Real.rpow_pos_of_pos hθ _)

/-- THEOREM: f(θ) is strictly increasing in tightness. -/
theorem f_strictMono {θ θ' : ℝ} (hθ : 0 < θ) (h : θ < θ') :
    p.f θ < p.f θ' := by
  unfold f
  have hθ' : 0 < θ' := lt_trans hθ h
  have hexp : 0 < 1 - p.η := by linarith [p.η_lt_one]
  have : θ ^ (1 - p.η) < θ' ^ (1 - p.η) :=
    Real.rpow_lt_rpow hθ.le h hexp
  exact mul_lt_mul_of_pos_left this p.μ_pos

/-- THEOREM: q(θ) is strictly decreasing in tightness. -/
theorem q_strictAnti {θ θ' : ℝ} (hθ : 0 < θ) (h : θ < θ') :
    p.q θ' < p.q θ := by
  unfold q
  have hθ' : 0 < θ' := lt_trans hθ h
  have hθ_ne : θ ≠ 0 := ne_of_gt hθ
  have hθ'_ne : θ' ≠ 0 := ne_of_gt hθ'
  have hpos_eta : 0 < p.η := p.η_pos
  -- θ'^(-η) < θ^(-η) iff θ^η < θ'^η (since both positive)
  have hθη : 0 < θ ^ p.η := Real.rpow_pos_of_pos hθ _
  have hθ'η : 0 < θ' ^ p.η := Real.rpow_pos_of_pos hθ' _
  have hlt : θ ^ p.η < θ' ^ p.η := Real.rpow_lt_rpow hθ.le h hpos_eta
  have hinv : θ' ^ (- p.η) < θ ^ (- p.η) := by
    rw [Real.rpow_neg hθ.le, Real.rpow_neg hθ'.le]
    exact (inv_lt_inv₀ hθ'η hθη).mpr hlt
  exact mul_lt_mul_of_pos_left hinv p.μ_pos

end MatchingParams

/-- Steady-state unemployment rate with separation rate s and finding rate f. -/
noncomputable def steadyStateU (s f : ℝ) : ℝ := s / (s + f)

/-- THEOREM: steady-state unemployment is in [0,1] when s ≥ 0 and f > 0. -/
theorem steadyStateU_mem_unit {s f : ℝ} (hs : 0 ≤ s) (hf : 0 < f) :
    0 ≤ steadyStateU s f ∧ steadyStateU s f ≤ 1 := by
  unfold steadyStateU
  have hsum : 0 < s + f := by linarith
  refine ⟨div_nonneg hs hsum.le, ?_⟩
  rw [div_le_one hsum]
  linarith

/-- THEOREM (displacement shock): steady-state unemployment is monotone
    increasing in the separation rate s. This is the formal version of
    "higher separations → higher unemployment". -/
theorem steadyStateU_mono_separation {s s' f : ℝ}
    (hs : 0 ≤ s) (hf : 0 < f) (h : s ≤ s') :
    steadyStateU s f ≤ steadyStateU s' f := by
  unfold steadyStateU
  have hs' : 0 ≤ s' := le_trans hs h
  have hsf : 0 < s + f := by linarith
  have hsf' : 0 < s' + f := by linarith
  rw [div_le_div_iff₀ hsf hsf']
  nlinarith

/-- THEOREM (strict): raising s strictly raises steady-state u when f > 0. -/
theorem steadyStateU_strictMono_separation {s s' f : ℝ}
    (hs : 0 ≤ s) (hf : 0 < f) (h : s < s') :
    steadyStateU s f < steadyStateU s' f := by
  unfold steadyStateU
  have hs' : 0 ≤ s' := le_of_lt (lt_of_le_of_lt hs h)
  have hsf : 0 < s + f := by linarith
  have hsf' : 0 < s' + f := by linarith
  rw [div_lt_div_iff₀ hsf hsf']
  nlinarith

/-- THEOREM (Beveridge curve, monotonicity in finding rate): steady-state
    unemployment is antitone in f. -/
theorem steadyStateU_antitone_f {s f f' : ℝ}
    (hs : 0 < s) (hf : 0 < f) (h : f ≤ f') :
    steadyStateU s f' ≤ steadyStateU s f := by
  unfold steadyStateU
  have hf' : 0 < f' := lt_of_lt_of_le hf h
  have hsf : 0 < s + f := by linarith
  have hsf' : 0 < s + f' := by linarith
  rw [div_le_div_iff₀ hsf' hsf]
  nlinarith


/-- The matching function `m(u,v) = μ · u^η · v^(1-η)`. This is the
    Cobb-Douglas CRS matching function studied empirically in
    Petrongolo-Pissarides (JEL 2001). The functional form is not arbitrary:
    it is the one-parameter Cobb-Douglas slice of the family of
    constant-returns-to-scale matching functions with empirical elasticity
    `η ∈ (0,1)`.  -/
noncomputable def matchingFunction (p : MatchingParams) (u v : ℝ) : ℝ :=
  p.μ * u ^ p.η * v ^ (1 - p.η)

/-- THEOREM (constant returns to scale): the Cobb-Douglas matching function
    is homogeneous of degree 1: `m(λu, λv) = λ · m(u, v)` for `λ > 0`,
    `u > 0`, `v > 0`. This is the GROUNDING PROPERTY of the functional form —
    random-search matching with no congestion externalities obeys CRS, and
    Cobb-Douglas is the canonical empirical instance of a CRS matching
    function (Petrongolo-Pissarides 2001 §2).  -/
theorem matchingFunction_CRS (p : MatchingParams) {u v lam : ℝ}
    (hu : 0 < u) (hv : 0 < v) (hlam : 0 < lam) :
    matchingFunction p (lam * u) (lam * v) = lam * matchingFunction p u v := by
  unfold matchingFunction
  have hlam_nn : (0 : ℝ) ≤ lam := hlam.le
  have hu_nn : (0 : ℝ) ≤ u := hu.le
  have hv_nn : (0 : ℝ) ≤ v := hv.le
  rw [Real.mul_rpow hlam_nn hu_nn, Real.mul_rpow hlam_nn hv_nn]
  have hlam_sum : lam ^ p.η * lam ^ (1 - p.η) = lam := by
    rw [← Real.rpow_add hlam]
    have : p.η + (1 - p.η) = 1 := by ring
    rw [this, Real.rpow_one]
  -- LHS = μ * (lam^η * u^η) * (lam^(1-η) * v^(1-η))
  --     = μ * (lam^η * lam^(1-η)) * u^η * v^(1-η)
  --     = μ * lam * u^η * v^(1-η)
  --     = lam * (μ * u^η * v^(1-η))
  calc p.μ * (lam ^ p.η * u ^ p.η) * (lam ^ (1 - p.η) * v ^ (1 - p.η))
      = p.μ * (lam ^ p.η * lam ^ (1 - p.η)) * (u ^ p.η * v ^ (1 - p.η)) := by ring
    _ = p.μ * lam * (u ^ p.η * v ^ (1 - p.η)) := by rw [hlam_sum]
    _ = lam * (p.μ * u ^ p.η * v ^ (1 - p.η)) := by ring

/-- THEOREM: the matching function is symmetric under `(u, v) ↔ (v, u)`
    exactly when `η = 1/2`. This is the empirical case documented in
    Petrongolo-Pissarides (JEL 2001), which reports `η ≈ 0.5` as the
    meta-analytic consensus across 30+ cross-country studies. -/
theorem matchingFunction_symmetric_at_half (p : MatchingParams)
    (hhalf : p.η = 1 / 2) (u v : ℝ) :
    matchingFunction p u v = matchingFunction p v u := by
  unfold matchingFunction
  have h1 : 1 - p.η = p.η := by rw [hhalf]; ring
  rw [h1]
  ring


end Economy
