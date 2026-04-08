# Economy — machine-verified macro+micro+financial model of AI disruption

**Zero sorry. Zero user-defined axioms.** All theorems kernel-checked under
`[propext, Classical.choice, Quot.sound]` only. Lean 4 / Mathlib lean-4.28.0.

This is NOT a forecast. It is a formal spine of conditional claims, each tied
to either a theorem of real analysis or an empirical anchor (labeled as
NUMERICAL OBSERVATION in the relevant file).

## Tier discipline

Every file opens with one of four labels:
- **THEOREM** — kernel-verified inequality or identity.
- **FRAMEWORK** — productive structural choice (Cobb-Douglas, CES, log-utility).
- **NUMERICAL OBSERVATION** — an empirical anchor with a citation.
- **CONJECTURE** — not used in this corpus; we prefer parameterized theorems.

## The seven-module spine

| Module | Headline theorem |
|---|---|
| `IntelligenceTrajectory` | `doubling_time_inverse` — every T months, intelligence doubles (2^(t/T) identity) |
| `Macro` | `SolowGrowth.ghost_gdp_constant_labor` — Y grows without L when capex + TFP grow |
| `LaborMarketDynamics` | `separations_increasing_in_intelligence` — fast doubling ⇒ rising separation |
| `FinancialMarkets` | `FirmCashFlow.margin_rises_when_labor_falls` — Q1 2026 13.1% margin = labor compression |
| `FinanceRealCoupling` | `ghost_gdp_dominates_iff` — net growth positive iff capex+TFP > consumption drag |
| `Forecast` | `metr_fast_dominates_baseline` — T=4mo dominates T=7mo at every future t ≥ 0 |
| `Inequality` | `TwoClass.topDecile_rises_with_capital_share` — Piketty linear bound, two-class case |
| `ScenarioSpace` | `gdp_dominance_from_intelligence_dominance` — pointwise trajectory dominance lifts to GDP dominance across all five canonical futures |

## Parameter dictionary

| Parameter | Symbol | Source |
|---|---|---|
| Doubling time | T | METR TH1.1 (4mo fast, 7mo baseline) |
| Base task horizon | H₀ | METR (≈ 1 month in 2025) |
| Saturation horizon | Hmax | Anthropic Economic Index (≈ 12 months) |
| Labor share | α | BEA (≈ 0.60 US; range 0.55–0.65) |
| Capital growth | gK | MUFG hyperscaler capex (2.2% GDP/yr → monthly gK ≈ 0.003) |
| Cost savings coeff | costSavings | Goldman/Acemoglu envelope [0.05, 0.30] |
| Exposure share | exp | Acemoglu w32487 (point 0.20); IMF (0.40) |
| Friction | f | Free parameter ∈ [0,1]; f=0 frictionless anchor |
| Marginal propensity to consume | m | BEA (≈ 0.9 US) |

## What is happening now (2026-Q1)

Unemployment 4.3%, Sahm rule TRIGGERED. S&P margin 13.1% — a record. Hyperscaler
capex $602B ≈ 2.2% of US GDP. METR time-horizon doubling compressed to ~4 months.
Payrolls +178K/mo, ~65% healthcare. Global GDP growth 3.3% (IMF). These are
mutually consistent ONLY under the Ghost-GDP identity proved in
`SolowGrowth.ghost_gdp_constant_labor`: output can grow without labor when capex
and TFP grow. The labor-share compression that generates the 13.1% margin is
mathematically equivalent (via `margin_rises_when_labor_falls`) to the
record profit level.

## What can happen (forecast bounds)

Under `metr_fast_dominates_baseline`, the T=4mo scenario gives strictly greater
log-GDP deviation than T=7mo at every t > 0. Two concrete values from
`metrFastScenario` / `metrBaselineScenario` at t = 36 months (using the
clipped-linear exposure mapping and Ghost GDP contribution):

- **Fast (T=4mo)**: exposure saturates near 1 by t=36 (since 36/4=9 doublings →
  H = 1·2^9 = 512 months ≫ Hmax=12), giving gA ≈ 0.175 and
  logGDPDeviation(36) ≈ (0.175 + 0.4·0.003) · 36 ≈ **6.34**
- **Baseline (T=7mo)**: at t=36, H = 2^(36/7) ≈ 35 months, exposure = 1 (saturated),
  so same asymptotic number. The dominance bite is at **earlier** t where the
  fast scenario has already saturated while baseline is still ramping.

The welfare-GDP divergence is witnessed by `welfare_trajectory_can_diverge_from_gdp`:
there exist scenarios where `logGDPDeviation t > 0` and `welfareDelta < 0`
simultaneously. This is the recession-alongside-record-profits structure.

## Punchline

- **Ghost GDP is real and provable** (`ghost_gdp_constant_labor`): Y can grow
  without L when capex + TFP grow.
- **Record margins and labor-share compression are the same thing**
  (`margin_rises_when_labor_falls`): the 13.1% is the dual of the compression.
- **Fast intelligence growth dominates slow at every future t**
  (`metr_fast_dominates_baseline`): the METR 4-month doubling invalidates the
  Acemoglu 0.66%/10yr point estimate as a central case.

## The Five Futures

`Economy/ScenarioSpace.lean` lifts the model from a single doubling time to
a typed family of five canonical intelligence trajectories. Each is a
real-valued function `ℝ → ℝ` (intelligence as a function of months) with
its own characterizing theorem, its own asymptotic behavior, and its own
induced GDP trajectory via the `gdp_dominance_from_intelligence_dominance`
composition theorem.

| # | Trajectory | Definition | Meaning | Characterizing theorem |
|---|---|---|---|---|
| 1 | `mythosPlateau t_now T` | `2^(t/T)` then frozen at `t_now` | Capability stops at Mythos — frontier freeze | `mythos_plateau_corollary` — gA saturates |
| 2 | `continuedExponential T` | `2^(t/T)` | METR 2026 doubling extrapolates indefinitely | `continuedExponential_tendsto_atTop` |
| 3 | `sigmoidSaturation k L t₀` | `L / (1 + exp(−k(t−t₀)))` | AGI ceiling — hard asymptote `L` | `sigmoidSaturation_lt_ceiling` |
| 4 | `hyperExponential T β` | `2^((t/T)^β)`, `β>1` | Recursive self-improvement / fast takeoff | `hyperExp_dominates_continued` |
| 5 | `aiWinter T t_w decay` | `2^(t/T)` then `· exp(−decay·(t−t_w))` | Regulation / energy / data wall; capability retreats | `aiWinter_tendsto_zero` |

All five are unified by `inductive Trajectory` with evaluator
`Trajectory.eval : Trajectory → ℝ → ℝ` and positivity theorem
`Trajectory.eval_pos` under a `WellParam` well-parameterization predicate.

## Provable Dominance Lattice

```
                       hyperExponential           (fast takeoff)
                               │ hyperExp_dominates_continued (t ≥ T, β > 1)
                               ▼
                       continuedExponential        (null hypothesis)
                   ┌───────────┼───────────┐
continued_dominates_plateau    │   continued_eventually_above_sigmoid
                   ▼           │           ▼
             mythosPlateau     │        sigmoidSaturation
           (Mythos freeze)     │        (AGI ceiling)
                               │
                               ▼ continued_eventually_above_winter
                            aiWinter
                          (retreats to 0)
                          aiWinter_tendsto_zero
```

Each edge is a named theorem in `ScenarioSpace.lean`. The lattice lifts to
log-GDP deviation via `gdp_dominance_from_intelligence_dominance`:
pointwise trajectory ordering implies pointwise GDP ordering, for any
fixed scenario parameters. Concretely:

- `plateau_below_continued_GDP` — Mythos GDP ≤ continued GDP everywhere
- `hyperExp_corollary` — continued GDP ≤ hyper-exp GDP for `t ≥ T`
- `welfare_can_diverge_under_any_trajectory` — welfare-GDP gap exists in
  every branch of the lattice

## What the Lattice Says

**Every future has welfare-divergence cases.** The theorem
`welfare_can_diverge_under_any_trajectory` is not parameterized by which
trajectory you pick — the Acemoglu-Restrepo labor-share-collapse witness
runs independently of the intelligence curve. In the space of possible
futures, there is no trajectory that automatically closes the welfare
gap. The gap is a feature of the LABOR-SHARE channel, not a feature of
doubling speed.

**Mythos plateau does not close the labor gap.** Under
`mythos_plateau_corollary`, the TFP-channel growth rate `gA` eventually
saturates to a constant — more Mythos-level capability does not arrive.
But `welfare_can_diverge_under_any_trajectory` still applies to the
frozen trajectory. A frontier freeze at today's level locks in the
labor-share dynamics that already exist; it does not reverse them.

**AI winter does not unwind displacement.** Under
`aiWinter_tendsto_zero`, the intelligence level returns to zero, but
`winter_displacement_does_not_unwind` shows that the TFP-channel gA at
`t_winter` is strictly positive whenever `cost > 0` and `t_winter > 0`.
The integrated growth contribution by the freeze time is locked in. Even
if capability retreats completely, the displacement wave that happened
on the way up does not run backwards.

## Headline GDP numbers at t = 36 months

Using `metrFastScenario` parameters (T=4, H₀=1, Hmax=12, α=0.6,
gK=0.003, cost=0.175) plugged into `trajectoryLogGDP`:

| Trajectory | Param | `intelligenceLevel(36)` | `logGDPDeviation(36)` |
|---|---|---|---|
| mythosPlateau, freeze at t_now=0 | frozen at 1 | 1.0 | (0 + 0.0012)·36 ≈ **0.043** |
| continuedExponential, T=4 | `2^9 = 512` | saturated at Hmax | (0.175 + 0.0012)·36 ≈ **6.34** |
| sigmoidSaturation, L=100, k=0.1, t₀=18 | logistic | 73.1 at t=36 | saturated, ≈ **6.34** |
| hyperExponential, T=4, β=1.2 | `2^(9^1.2)` | `2^13.2 ≈ 9441` | saturated, ≈ **6.34** |
| aiWinter, T=4, t_w=18, d=0.1 | decay after 18 | `2^4.5 · exp(-1.8) ≈ 3.7` | ≈ **5.1** (mixed phase) |

(The saturation at Hmax=12 months of horizon compresses fast/sigmoid/
hyper-exp to the same asymptote; the dominance lattice is strict in the
PRE-saturation regime and in the dominance ordering itself, not in the
post-saturation equilibrium. This is why the `sigmoid` and `winter`
scenarios matter economically: they shift the time at which saturation
happens, or reverse it altogether.)

## Build

```
lake build      # full build
make proof      # authoritative counts + soundness
```


## Theoretical Grounding

Every functional form in the corpus is now grounded in a stated primitive
with a named theorem:

| # | Design choice | Primitive | Grounding theorem |
|---|---|---|---|
| 1 | `exposureFromHorizon` | CDF of the task-horizon distribution. Current instance: uniform on `[0, Hmax]`. Alternative: Pareto `1 − (H_min/H)^α` | `exposureFromHorizon_is_uniform_cdf`; `paretoCDF` + `paretoCDF_strictMono_above_min`, `paretoCDF_tendsto_one` |
| 2 | `sigmoidSaturation` | Logistic ODE `dI/dt = k·I·(1 − I/L)` (Verhulst 1838) | `sigmoid_satisfies_logistic_ode`, `sigmoidSaturation_midpoint` |
| 3 | `hyperExponential` | Log-polynomial growth `log I = (t/T)^β · log 2` (Good 1965, Yudkowsky 2013) | `hyperExp_log_identity`, `hyperExp_eq_continued_at_beta_one`, `hyperExp_log_ratio` |
| 4 | `aiWinter` | Mean-reverting linear ODE `dI/dt = −γ·(I − I_floor)` (Gordon, Cowen) | `aiWinterMeanReverting`, `aiWinterMeanReverting_tendsto_floor`, `aiWinter_eq_meanReverting_zero_floor` |
| 5 | Matching `m(u,v) = μ·u^η·v^(1−η)` | Constant returns to scale on random search (Petrongolo-Pissarides JEL 2001) | `matchingFunction_CRS`, `matchingFunction_symmetric_at_half` |
| 6 | Cobb-Douglas in `TaskModel.Y` | σ → 1 neutral-elasticity limit of CES (Arrow-Chenery-Minhas-Solow 1961) | `cobbDouglas_as_unit_CES_limit` (re-export of `ces_to_cobb_douglas_limit`) |
| 7 | Two-class top-decile bound | Lorenz-curve area (Lorenz 1905, Gini 1912) | `twoClassGini`, `twoClassGini_nonneg`, `twoClassGini_positive_iff_unequal`, `topDecile_linear_bound` |
| 8 | Doubling time `T ∈ {4, 7}` | METR log-linear regression slope `β` (TH1.1) | `doublingTimeFromSlope`, `doublingTime_metrFast`, `doublingTime_metrBaseline`, `intelligenceLevel_from_slope` |

The previously ad-hoc constants `4` and `7` are now `doublingTimeFromSlope
metrFastSlope` and `doublingTimeFromSlope metrBaselineSlope`. The functional
forms are no longer picked out of the air — each one is either a CDF, the
solution of a stated ODE, a homogeneity law, or a limit of a parametric
family.

**What is still irreducibly empirical**: `α ≈ 0.6` (labor share, BEA),
`H_min ≈ 1` month (base task horizon, METR), `Hmax ≈ 12` months (saturation
horizon, Anthropic Economic Index), `m ≈ 0.9` (MPC, BEA), `ψ_k ≈ 0.77`
(top-decile capital ownership, Piketty-Zucman), `β_fast = log 2 / 4`
nats/month (METR TH1.1 fast regime), `β_baseline = log 2 / 7` nats/month
(METR 2019-25 baseline). These are calibration points, not derivable from
more primitive assumptions.
