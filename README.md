<p align="center">
  <img src="brand/wordmark-display.svg" alt="Awkronos" height="48">
</p>

# economy

**The math behind [tim.awkronos.com/economy](https://tim.awkronos.com/economy).**

The structural math behind every number on that page is a theorem in this repository; the scenario percentages are arithmetic that plugs the calibration in `Economy/Calibration.lean` into those theorems. Lean 4 +
Mathlib. Current compiler and soundness status lives only in the `economy` row
of `/tmp/proof-report.json`; this README keeps the stable theorem citations.

If you got here from the blog post and just want to find the number you were reading about, start with the [Receipts](#receipts) section below.

---

## What this actually is

The blog post at tim.awkronos.com/economy makes three kinds of claims.

1. **Empirical numbers** — 4.3% unemployment (BLS Employment Situation, March 2026), 13.1% S&P 500 net profit margin (FactSet, Q1 2026), $602B hyperscaler AI capex (MUFG / CreditSights, 2026), and the METR task-horizon curve (TH1.1, January 2026 — 7 seconds of task length in 2019, doubling every ~4 months since 2024). These come from BLS, FactSet, MUFG, and METR. They are observed facts, not model outputs; `REFERENCES.md` dates every one, and the page may carry a newer release of the same anchor.

2. **Structural math** — "When labor is flat and both productivity and capital grow, output still grows" (`SolowGrowth.ghost_gdp_nonneg`). "With complementary tasks — elasticity of substitution below 1 — aggregate output stays strictly below a ceiling set by labor, for every finite capital level" (`ces_sigma_lt_one_capital_ceiling`). "The faster METR doubling path weakly dominates the slower baseline path in log-GDP deviation at every future time" (`metr_fast_dominates_baseline`). These are **theorems** in this repository, proved in Lean 4 — no `sorry`, no user-defined axioms — and every assumption a theorem needs appears in its stated signature.

3. **Scenario outputs** — "Under the METR fast-doubling path at 36 months, GDP rises +30.9% and median consumption falls −21.0%." These come from **plugging real numbers into the structural math**. The calibration is one small file (`Economy/Calibration.lean`). You can change the numbers and recompile.

The point of this repository is that all three layers are separable. If you think the calibration is wrong, change it and see what happens. If you think the model is wrong, you can point at a specific theorem and say "this one is too strong" or "this one is false." If you think an empirical number is out of date, you can update it in one place.

## What it isn\'t

- Not a forecast of unemployment. The model does not predict unemployment numbers. It predicts *shapes* — under these assumptions, the labor-share trajectory goes like this.
- Not a claim that AI is good or bad. It is a claim that the current numbers are self-consistent under a specific mathematical framework.
- Not a DSGE model or a macroeconometric forecast. It is a small structural model with transparent assumptions.

## Receipts

Every underlined number in the blog post is a tooltip that shows the file and line of the theorem behind it. Here are the most important ones.

| Number on the blog | Theorem | File |
|---|---|---|
| "2^9 = 512× task horizon at 36 months" | `pipeline_metr_horizon_36mo` | [`Economy/EndToEndForecast.lean`](Economy/EndToEndForecast.lean) |
| "GDP up 4 percent with flat hiring" | `SolowGrowth.ghost_gdp_constant_labor` (derived instance: `SolowGrowth.ghost_gdp_ofCobbDouglasPaths`) | [`Economy/Macro.lean`](Economy/Macro.lean) |
| "Welfare can fall while GDP rises" | `welfare_can_fall_with_gdp_rise` | [`Economy/Welfare.lean`](Economy/Welfare.lean) |
| "+30.9% → +22.9%, bubble-pop haircut" | `bubble_pop_ghost_gdp_loss` | [`Economy/CapexBubble.lean`](Economy/CapexBubble.lean) |
| "+30.9% → +22.4%, non-substitutable floor" | `jobSwap_cobbDouglas_zero_Lnon_limit` | [`Economy/JobSwapping.lean`](Economy/JobSwapping.lean) |
| "1.35% expected recession drag" | `recession_expected_loss` + `recession_BEA_expected_36mo` | [`Economy/RecessionShock.lean`](Economy/RecessionShock.lean) |
| "Fast doubling dominates baseline" | `metr_fast_dominates_baseline` | [`Economy/Forecast.lean`](Economy/Forecast.lean) |
| "Profit margins rise as labor share falls" | `FirmCashFlow.margin_rises_when_labor_falls` | [`Economy/FinancialMarkets.lean`](Economy/FinancialMarkets.lean) |

These are the fully qualified names in the compiled corpus: prefix them with `Economy.` (and the shown `SolowGrowth.` / `FirmCashFlow.` namespace where present) and they resolve to a live declaration. The cited theorems carry the **formulas**; the percentages are arithmetic on those formulas at the `calBEA2026` numbers (e.g. "4 percent" is `(1 − 0.6) · 0.003 · 36 ≈ 4.3%` through the ghost-GDP identity with `gA = gL = 0`). Two exceptions, stated honestly: the 1.35% recession drag is evaluated in-kernel by `recession_BEA_expected_36mo` (`= 135/10000` exactly); the +30.9% / −21.0% / +22.9% / +22.4% scenario outputs are computed by the blog page's forecast engine plugging the calibration into these identities — there is no Lean declaration that prints those four figures.

## The model in one page

The foundation is **Cobb-Douglas production**:

```
Y = A · K^(1−α) · L^α
```

where `Y` is output, `A` is productivity, `K` is capital, `L` is labor, and `α ≈ 0.6` is labor\'s share of income. This is a 1928 formula, still the workhorse of applied macroeconomics, and it has a surprising property: it is **concave in each input**. Halving the workforce only drops output by about a third.

From that foundation, the model adds five layers.

1. **Intelligence trajectory** (`Economy/IntelligenceTrajectory.lean`, `Economy/ScenarioSpace.lean`). AI capability doubles every `T` months: `2^(t/T)` (T = 4 on the fast path, 7 on the baseline). The doubling-time slider on the blog controls `T`. `Economy/ScenarioSpace.lean` formalizes five canonical shapes — plateau, continued exponential, sigmoid saturation, hyper-exponential, AI winter — with dominance theorems between them.

2. **Task exposure** (`Economy/TaskModel.lean`). As AI capability grows, the fraction of human tasks AI can do also grows. Exposure saturates at 1.0 when AI can do every job in the distribution.

3. **Labor market** (`Economy/LaborMarketDynamics.lean`, `Economy/MatchingModel.lean`, `Economy/LaborShare.lean`). A Mortensen-Pissarides matching function turns exposure into displacement. Labor share falls as capital and productivity carry more of the load.

4. **Financial markets** (`Economy/FinancialMarkets.lean`, `Economy/FinanceRealCoupling.lean`, `Economy/CapexBubble.lean`). Capital growth is funded by hyperscaler capex. The debt sustainability of that capex is modeled explicitly so the model breaks honestly when the bubble stops.

5. **Welfare and inequality** (`Economy/Welfare.lean`, `Economy/Inequality.lean`). Aggregate GDP is not the same as median consumption. A two-class Lorenz model shows how the gap opens.

Three failure modes are modeled explicitly:

- **JobSwapping** — a CES nest over `(capital + AI-substitutable labor)` and `non-substitutable labor`. In the ρ → 0 Cobb-Douglas limit, output is `(K + A·L_sub)^α · L_non^(1−α)`: if the non-substitutable bucket `L_non` shrinks to zero, output goes to zero with it even at a fixed positive augmented capital stack (`jobSwap_cobbDouglas_zero_Lnon_limit`), and while `L_non` is positive, output is strictly positive (`jobSwap_welfare_lower_bound`). At 25% non-sub, the page's forecast engine shows the 36-month GDP gain falling from +30.9% to +22.4%.
- **RecessionShock** — a Poisson recession regime with hazard 0.015/mo, duration 10 months, shock 0.0025. Expected 36-month drag: 1.35%.
- **CapexBubble** — a debt-sustainability switch on hyperscaler capex. When debt service exceeds cash-flow growth, K drops from hyperscaler rates to maintenance rates. 36-month GDP gain falls +30.9% → +22.9%.

## Running it yourself

```bash
git clone https://github.com/awktavian/economy
cd economy
make proof
```

`make proof` runs `~/.claude/scripts/open-math.py verify --project economy
--report /tmp/proof-report.json --sidecar /tmp/open_math.json`, refreshing and
verifying against the single estate report. Read its `economy` row for current
build, coverage, declaration, and axiom-accounting results.

To check a specific theorem's axiom dependencies:

```bash
printf 'import Economy.EndToEndForecast\n#print axioms Economy.pipeline_metr_horizon_36mo\n' | lake env lean --stdin
```

You should see `depends on axioms: [propext, Classical.choice, Quot.sound]` — the three foundational axioms of Lean 4. Nothing else. If you see anything more, that theorem has a hidden dependency and the soundness claim is false for it.

## Changing the calibration

Every empirical parameter is in `Economy/Calibration.lean`. The three canonical calibrations are `calBEA2026`, `calBaseline`, and `calPessimistic`. Each is a `ModelCalibration` struct with fields like:

- `α` — labor\'s share of national income (BEA: 0.60)
- `H_min` — shortest task length AI can handle today (METR baseline: 1 month unit)
- `H_max` — saturation horizon (AEI exposure data: 12 months)
- `β_slope` — METR regression slope in nats/month (current fast: log 2 / 4)
- `gK` — capital growth rate per month (hyperscaler-driven: 0.003)
- `costSavings` — task cost-savings coefficient per unit exposure (0.175; the Goldman-corner value — 0.40 exposure × 0.175 = the ~7% anchor — while the Acemoglu corner uses 0.033)
- `nonSubShare` — non-AI-substitutable labor fraction (BLS + ILO: 0.25)
- `recessionHazard` — monthly recession hazard (NBER post-1950: 0.015)
- `debtStack` — hyperscaler debt (~$400B)

Every field is subtype-constrained to a plausible range. Violating those bounds is a type error, not a runtime error. Change one number, recompile, see the effect.

## Tier discipline

Every file opens with a tier label.

- **THEOREM** — machine-verified inequality or identity. Proved facts about real numbers.
- **FRAMEWORK** — a productive structural choice (Cobb-Douglas, CES, log-utility). Lenses, not facts.
- **NUMERICAL OBSERVATION** — an empirical anchor with a citation. True until the next BLS release.

Never confuse tiers. A framework claim stated as a theorem is a lie.

## Directory layout

```
Economy/
  Basic.lean                   types: ExposureShare, Elasticity
  Calibration.lean             ModelCalibration + three canonical calibrations + V1-V6 validations
  IntelligenceTrajectory.lean  exponential doubling dynamics + task-horizon/exposure maps
  TaskModel.lean               Cobb-Douglas foundation + Hulten\'s theorem
  CES.lean                     CES aggregation + σ→1 limit to Cobb-Douglas
  Exposure.lean                task-exposure aggregation
  Macro.lean                   Solow growth + Ghost GDP identity + factor-income Euler
  Productivity.lean            TFP bound from task exposure
  LaborMarket.lean             two-sector labor model
  GDP.lean                     first-order GDP delta from TFP + employment
  LaborShare.lean              labor-share dynamics
  LaborMarketDynamics.lean     separations, Beveridge, Sahm rule
  MatchingModel.lean           Mortensen-Pissarides matching function
  Services.lean                Baumol cost disease
  FinancialMarkets.lean        profit margins, PV, equity channel
  FinanceRealCoupling.lean     capex-earnings-consumption feedback
  ScenarioSpace.lean           five-trajectory scenario lattice with dominance
  Forecast.lean                scenario → GDP delta composition
  Welfare.lean                 log-utility + welfare-can-fall witness
  Inequality.lean              two-class Gini + top-decile propagation
  Empirical.lean               BLS / Brynjolfsson / MUFG anchors
  Bounds.lean                  Acemoglu low and Goldman high envelope
  Sensitivity.lean             monotonicity in each calibration parameter
  EndToEndForecast.lean        5 pipeline tests composing the whole corpus
  JobSwapping.lean             two-bucket non-substitutable labor floor
  RecessionShock.lean          Poisson regime-switching recession
  CapexBubble.lean             debt sustainability + Ghost GDP loss bound
  forecasts/                   output tables
REFERENCES.md                  every empirical source
```

## References

Every empirical number has a citation in [`REFERENCES.md`](REFERENCES.md). The biggest load-bearing sources:

- **BLS Employment Situation** (March 2026) — unemployment, labor force, payroll
- **FactSet Earnings Insight** (Q1 2026) — S&P profit margins
- **MUFG / CreditSights** (2026) — $602B AI capex, ~$400B hyperscaler debt stack
- **METR Task Horizon Benchmark TH1.1** (January 2026) — the task-horizon doubling curve (7 seconds in 2019; ~4-month doubling 2024–25)
- **Brynjolfsson, Chandar, Chen, "Canaries in the Coal Mine"** (Stanford, August 2025) — 6-13% older-worker gain vs younger-worker loss
- **Acemoglu, "The Simple Macroeconomics of AI"** (NBER wp32487, 2024) — task-based productivity bound
- **BEA NIPA** — US labor share α ≈ 0.60

## License

MIT. Use it, fork it, argue with it. If you find a calibration you believe in more than the ones in this repo, open a PR with the new numbers and the citation.

## Author

Tim Jacoby, Awkronos. The blog post is at [tim.awkronos.com/economy](https://tim.awkronos.com/economy).

*The same math that signed this off would sign off on the thing you\'ve been meaning to build.*
