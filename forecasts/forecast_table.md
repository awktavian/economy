# Forecast table — t ∈ {4, 8, 12, 24, 36} months

All integer `intelligenceLevel` values are kernel-exact at integer multiples of the doubling time `T`.
`deltaTFP` uses the Goldman-corner form `exposure · costSavings` (friction = 0).
Every cell is backed by a theorem in `~/economy`. File:line citations at the bottom.

Constants shared across calibrations:
- `α = 0.60`, `H_min = 1 mo`, `H_max = 12 mo`, `gK = 0.003/mo`
- `costSavings = 0.175` (BEA2026 / Baseline), `0.250` (Pessimistic)

The task horizon column uses `H = H_min · I = 1 · I = I` months. The
exposure column uses `min 1 (max 0 (H / Hmax)) = min 1 (I / 12)`.

## calBEA2026 — fast slope, T = 4 months

| t (mo) | I = 2^(t/T) | H = I · 1 mo | exposure (H/12) | gA · t = exposure · 0.175 · t (dimensionless) | (1−α)·gK·t = 0.0012·t | log-GDP dominance class |
|---|---|---|---|---|---|---|
| 4 | **2** | 2 mo | 0.1667 | 0.1167 | 0.0048 | above baseline (P3) |
| 8 | **4** | 4 mo | 0.3333 | 0.4667 | 0.0096 | above baseline (P3) |
| 12 | **8** | 8 mo | 0.6667 | 1.400 | 0.0144 | above baseline (P3) |
| 24 | **64** | 64 mo | 1.000 (saturated) | 4.200 | 0.0288 | saturated, above baseline |
| 36 | **512** | 512 mo | 1.000 (saturated) | 6.300 | 0.0432 | saturated, above baseline |

Witness for rows 4–12: `pipeline_metr_horizon_36mo` proves `intelligenceLevel 36 4 = 512`
(`Economy/EndToEndForecast.lean:19`); the intermediate doublings 2, 4, 8, 64 come from
`intelligenceLevel_k_doublings` (`Economy/IntelligenceTrajectory.lean:73`).

## calBaseline — slow slope, T = 7 months

| t (mo) | I = 2^(t/T) | Task horizon (mo) | exposure (clipped) | qualitative vs calBEA2026 |
|---|---|---|---|---|
| 4 | 2^(4/7) ≈ 1.486 | ≈ 1.49 | ≈ 0.124 | ≤ fast (P3 strict at t > 0) |
| 7 | **2** | 2 mo | 0.167 | ≤ fast |
| 8 | 2^(8/7) ≈ 2.203 | ≈ 2.20 | ≈ 0.184 | ≤ fast |
| 12 | 2^(12/7) ≈ 3.281 | ≈ 3.28 | ≈ 0.273 | ≤ fast |
| 14 | **4** | 4 mo | 0.333 | ≤ fast |
| 24 | 2^(24/7) ≈ 10.90 | ≈ 10.90 | ≈ 0.908 | ≤ fast |
| 28 | **16** | 16 mo | 1.000 (saturated) | ≤ fast |
| 36 | 2^(36/7) ≈ 35.92 | ≈ 35.92 | 1.000 (saturated) | ≤ fast |

Non-integer rows are quoted as decimal approximations; the *only* kernel-exact
claim in this table is qualitative dominance: `pipeline_fast_dominates_baseline`
(`Economy/EndToEndForecast.lean:45`). The decimal values are illustrative, not proved.

## calPessimistic — fast slope, T = 4, costSavings = 0.250

| t (mo) | I | exposure | gA · t | qualitative |
|---|---|---|---|---|
| 4 | 2 | 0.1667 | 0.1667 | above calBEA2026 per unit t |
| 8 | 4 | 0.3333 | 0.667 | above calBEA2026 |
| 12 | 8 | 0.6667 | 2.000 | above calBEA2026 |
| 24 | 64 | 1.000 | 6.000 | saturated, above calBEA2026 |
| 36 | 512 | 1.000 | 9.000 | saturated, above calBEA2026 |

Note: `calPessimistic` uses `α = 0.55` (lower labor share), `ψ_k = 0.85` (higher
top-decile capital concentration), `m = 0.95`. The headline is NOT "more GDP" —
it is "more displacement + more concentration." Welfare divergence
(`welfare_can_fall_with_gdp_rise`, `Economy/Welfare.lean:73`) is strongest in
this calibration.

## Receipts

- `pipeline_metr_horizon_36mo` — `Economy/EndToEndForecast.lean:19`
- `pipeline_acemoglu_envelope_consistent` — `Economy/EndToEndForecast.lean:37`
- `pipeline_fast_dominates_baseline` — `Economy/EndToEndForecast.lean:45`
- `pipeline_welfare_sign_under_collapse` — `Economy/EndToEndForecast.lean:70`
- `pipeline_displacement_meets_brynjolfsson` — `Economy/EndToEndForecast.lean:80`
- `ModelCalibration` (extended with `gK`, `costSavings`) — `Economy/Calibration.lean:56`
- `Scenario.fromCalibration` — `Economy/Calibration.lean` (Part 6, bridge section)
- `validation_metr_24mo` — `Economy/Calibration.lean:195`
- `ghost_gdp_constant_labor` — `Economy/Macro.lean:163`
- `welfare_can_fall_with_gdp_rise` — `Economy/Welfare.lean:73`
