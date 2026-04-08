# economy

This project proves STRUCTURAL properties of a parameterized model. Parameters come from empirical literature cited in REFERENCES.md. This is not a proof of AI's impact on GDP.

What this project is:
- A Lean 4 / Mathlib formalization of the standard task-based production model used in Acemoglu (NBER w32487), with exposure shares, cost savings, frictions, and labor-market accounting as typed parameters.
- A set of ~20 kernel-checked structural theorems (monotonicity, tight bounds, Baumol transfer, sensitivity) that hold for ANY parameter values in the stated domains.

What this project is NOT:
- A prediction of GDP change.
- An empirical estimate. Empirical numbers (Acemoglu 0.66%, Brynjolfsson −6%, Goldman 7%) live in `REFERENCES.md` and are used only as anchors / envelope endpoints inside `Economy/Bounds.lean`, labeled `NUMERICAL OBSERVATION`.
- A welfare analysis.

## Layout

```
Economy.lean               — root
Economy/Basic.lean         — Occupation, Task, ExposureShare, Elasticity
Economy/Exposure.lean      — convex-combo aggregation, monotonicity
Economy/Productivity.lean  — Acemoglu/Hulten ΔTFP ≤ exposure·costSavings
Economy/LaborMarket.lean   — two-sector reinstatement vs displacement
Economy/GDP.lean           — gdpDelta monotonicity
Economy/Services.lean      — Baumol transfer
Economy/Bounds.lean        — Acemoglu 0.66% envelope, Goldman 7% high estimate
Economy/Sensitivity.lean   — partial-monotonicity lemmas
```

## Build

```
lake exe cache get  # fetch mathlib cache
lake build Economy
make proof          # writes /tmp/proof-report.json (tracked by Kagami)
```

## Theoretical Spine (added 2026-04-08)

The hardened theoretical core is built over seven modules, each with real economic content and a named headline theorem:

| Module | Headline theorem | Source |
|---|---|---|
| `Economy/TaskModel.lean` | `TaskEconomy.hulten_discrete` + `acemoglu_macro_bound` — Hulten's discrete log-decomposition and the Acemoglu (2024) macro bound as a corollary. | Hulten 1978, Acemoglu-Restrepo 2018, Acemoglu 2024 |
| `Economy/CES.lean` | `cesAggregate_homogeneous` — degree-1 homogeneity of CES; `sigmaToRho_pos_iff` — Acemoglu-Restrepo 2022 displacement-vs-productivity sign. CES→CD limit stated with one cited sorry. | ACMS 1961, Acemoglu-Restrepo 2022 |
| `Economy/LaborShare.lean` | `laborShare_strict_antitone_single` — strict fall in labor share from any automation increment on a positively-weighted task. | Acemoglu-Restrepo 2018, Karabarbounis-Neiman 2014 |
| `Economy/Services.lean` | `baumol_bowen_drag_strict` — aggregate growth strictly below progressive-sector growth; `baumol_nominal_share_rises` — inelastic-demand nominal share rise. | Baumol 1967, Baumol-Bowen 1966, Ngai-Pissarides 2007 |
| `Economy/MatchingModel.lean` | `steadyStateU_strictMono_separation` — displacement shocks strictly raise steady-state unemployment via the MP matching function; `f_strictMono`/`q_strictAnti` for the matching rates. | Mortensen-Pissarides 1994, Petrongolo-Pissarides 2001 |
| `Economy/Welfare.lean` | `welfare_can_fall_with_gdp_rise` — explicit witness that log-utility welfare can fall while GDP rises, via a collapsing labor share. | Acemoglu-Restrepo 2022, Acemoglu 2024 |
| `Economy/BoundsV2.lean` | `litBox_envelope` — the Acemoglu-Goldman literature envelope [0.0066, 0.07] sits inside the structural box [0.0075, 0.12] for any parameter tuple in the calibrated ranges. | Acemoglu 2024, IMF 2024, Goldman Sachs 2023 |

A supporting module `Economy/Empirical.lean` records the BCC 2025, Anthropic Economic Index, Acemoglu, and Goldman values as typed NUMERICAL OBSERVATION constants (not theorems), and proves trivial range-containment checks.

**State**: 16 files, 1470 lines, 76 theorems, 1 cited sorry (the CES→CD limit; `Economy/CES.lean:97`), 0 axioms, CLEAN under `#print axioms` (depends only on `propext`, `Classical.choice`, `Quot.sound`).
