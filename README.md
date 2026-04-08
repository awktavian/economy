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
