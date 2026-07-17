# Economy — theorem ladder (written 2026-07-17, per orchestration.md §Frontier-rung)

Compiler SSOT: 202 theorems, 0 sorry, 0 unchecked axioms (README claim;
`/tmp/proof-report.json` is the count authority). Three-layer discipline:
empirical inputs / structural theorems / calibration — separable by design.

## Rung 1 — R1 established, natural next closures

| # | Target | Why next | Est LOC |
|---|---|---|---|
| 1 | CES aggregate: elasticity σ < 1 ⇒ output floor as capital→∞ with labor fixed (sharper than "capital can't replace") | the floor theorem already exists in qualitative form | ~200 |
| 2 | Balanced-growth consistency: under Harrod-neutral tech progress, K/Y and interest rate are constant along BGP (Uzawa-adjacent) | structural spine extension | ~400 |
| 3 | Doubling-path dominance: any exponential task-horizon doubling dominates linear at every future t past explicit crossing time | README already claims the qualitative version | ~150 |
| 4 | Calibration-sensitivity: ∂(GDP uplift)/∂(task-horizon parameter) signed + bounded | makes scenario outputs differentiable-auditable | ~250 |

## Rung 2 — R1 multi-session

| # | Target | Est LOC |
|---|---|---|
| 5 | Two-sector model: automation sector + sheltered sector, Baumol cost-disease corollary | ~600 |
| 6 | Distributional layer: median vs mean consumption divergence under capital-share growth (formal Lorenz/Gini layer) | ~800 |

## Rung 3 — R2 open

None targeted. This repo's value is receipt-grade accounting of published
numbers, not open research. New empirical inputs enter via Calibration.lean only.

## Rung 4 — infrastructure

Receipts/doc sync with tim.awkronos.com/economy; no new scaffolding without a
rung-1/2 consumer. Cap ≤1/3.

## Discipline

Every blog number traces to a theorem or a labeled empirical input; raw
`#print axioms` with ESTABLISHED claims; no "derived" for compatibility checks.
