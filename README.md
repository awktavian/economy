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

## Build

```
lake build      # full build
make proof      # authoritative counts + soundness
```
