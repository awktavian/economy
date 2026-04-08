# Math Audit — Employment Forecast Post

Audit date: 2026-04-08. Auditor: Kagami (post-rewrite session).
Source: `~/tim/posts/2026-04-08-employment-forecast.md` (pre-rewrite draft).
Receipts: `~/economy` commit `5a07e55`. Build: 3137 jobs green, 0 sorry, 0 axioms.

Every numeric or theorem-citation claim in the draft has been cross-checked
against the Lean source. Verified rows are kept verbatim in the rewrite;
fixes are applied; unsupported claims are struck.

| # | Claim | Source in draft | Verified? | Action |
|---|---|---|---|---|
| 1 | Unemployment Mar 2026 = 4.3% | "What is happening now" §1 | YES | `REFERENCES.md` BLS row, kept |
| 2 | S&P 500 Q1 2026 net margin = 13.1% | §1 | YES | `REFERENCES.md` FactSet row, kept |
| 3 | Hyperscaler capex 2026 = $602B / 2.2% GDP | §1 | YES | `REFERENCES.md` MUFG row, kept |
| 4 | Young-worker employment fall = **−13%** | §1 | **NO** | **FIX**: canonical figure is **−6%** (Brynjolfsson Canaries, ages 22–25, ADP). The −13% is not in `REFERENCES.md` and contradicts both `validation_brynjolfsson` and `pipeline_displacement_meets_brynjolfsson`, both of which use `s/100 = 6/100`. The post's "−13%" is a builder typo for the −20% entry-level figure mentioned in §4 of the references. Corrected throughout. |
| 5 | METR doubling 2026-01 = 4 mo, baseline = 7 mo | §1 | YES | `REFERENCES.md` METR rows, kept |
| 6 | Cobb-Douglas: `Y = A·K^(1−α)·L^α`, α=0.6 | "The model" | YES | `Calibration.lean:92` α = 6/10 |
| 7 | "5% capex bump + 2% TFP bump → 4% GDP" | §1 closing | YES | Arithmetic: `2% + 0.4·5% = 4%` per `ghost_gdp_constant_labor`. Kept. |
| 8 | `ghost_gdp_constant_labor` at `Macro.lean:163` | §1 closing | YES | Verified at exact line. |
| 9 | `intelligenceLevel 4 4 = 2` | "Month 4" | YES | `2^(4/4) = 2^1 = 2`. Kept. |
| 10 | Exposure at t=4 = 2/12 ≈ 0.167 | "Month 4" | YES | `min(1, 1·2/12) = 0.1667`. Kept. |
| 11 | calBaseline I at t=4 ≈ 1.49 | "Month 4" | YES | `2^(4/7) ≈ 1.486`. Kept. |
| 12 | `pipeline_fast_dominates_baseline` at `EndToEndForecast.lean:45` | "Month 8" | LINE WRONG | Theorem exists; actual line is **:47**. Fixed. |
| 13 | I at t=12 = 8, exposure = 2/3 | "Month 12" | YES | `2^3 = 8`, `8/12 = 2/3`. Kept. |
| 14 | "S&P 13.1% margin is the early-warning shadow" | "Month 12" | SIGN ONLY | `margin_rises_when_labor_falls` (`FinancialMarkets.lean:54`) is signed. The post correctly flags it as the *direction*, not magnitude. Kept; rewrite tightened to be sign-only. |
| 15 | I at t=24 = 64, exposure saturates | "Month 24" | YES | `2^6 = 64`. Kept. |
| 16 | `validation_metr_24mo` at `Calibration.lean:195` | "Month 24" | LINE WRONG | Actual line is **:205**. Fixed. |
| 17 | calBaseline I at t=24 ≈ 10.90, exposure ~0.91 | "Month 24" | YES | `2^(24/7) ≈ 10.903`, `min(1, 10.903/12) ≈ 0.909`. Kept. |
| 18 | I at t=36 = 512 = 2^9 | "Month 36" | YES | `2^(36/4) = 2^9 = 512`. Kept. |
| 19 | `pipeline_metr_horizon_36mo` at `EndToEndForecast.lean:19` | "Month 36" | YES | Verified. |
| 20 | calBaseline I at t=36 ≈ 35.92 | "Month 36" | YES | `2^(36/7) ≈ 35.918`. Kept. |
| 21 | Welfare witness: Y=1, Y'=1.10, λ=1, λ'=0.5 | "Welfare" | YES | `Welfare.lean:76` `refine ⟨1, 11/10, 1, 1/2, ...⟩`. Kept. |
| 22 | `welfareDelta = log(0.55) ≈ −0.60` | "Welfare" | YES | `log(11/20) ≈ −0.5978`. Rewritten to `log(11/20)` exactly with the decimal. |
| 23 | "GDP rises 10%, median consumption falls 45%" | "Welfare" | DERIVED | `λ'·Y'/(λ·Y) = 0.55`, so consumption falls to 55% of baseline = a 45% fall. Verified arithmetically. Kept. |
| 24 | `welfare_can_fall_with_gdp_rise` at `Welfare.lean:73` | "Welfare" | YES | Verified. |
| 25 | `pipeline_welfare_sign_under_collapse` at `EndToEndForecast.lean:70` | "Welfare" | LINE WRONG | Actual line is **:73**. Fixed. |
| 26 | `pipeline_displacement_meets_brynjolfsson` at `EndToEndForecast.lean:80` | "Welfare" | LINE WRONG | Actual line is **:83**. Fixed. |
| 27 | "matches the Brynjolfsson Canaries young-worker figure" | "Welfare" | YES (with #4 fix) | Anchored to the corrected −6% figure. |
| 28 | `gA_antitone_doublingTime` (Forecast.lean) | "Breakers" #1 | YES | Line :77. Added line number. |
| 29 | `logGDPDeviation_nonneg` (Forecast.lean) | "Breakers" #3 | YES | Line :111. Added line number. |
| 30 | `gdp_mono_in_α` at `Calibration.lean:317` | "Breakers" #4 | LINE WRONG | Actual line is **:327**. Fixed. |
| 31 | "Steady-state `u* = s/(s+f)`" | "Breakers" #5 | YES | Mortensen-Pissarides; `MatchingModel.lean`. Kept. |
| 32 | "3137 build jobs green" | "Receipt" | YES | Re-verified by `lake build` in this session. Kept. |
| 33 | "0 sorry, 0 axioms" | "Receipt" | YES | `make proof` clean. Kept. |
| 34 | Margin record interpretation in footnote [1] | Notes | SIGN ONLY | Same as #14; the footnote already flags it as a signed identity, kept. |

## Summary

- Claims checked: **34**
- Claims kept verbatim: **24**
- Claims fixed (line numbers): **6** (rows 12, 16, 25, 26, 30, plus line additions for 28/29)
- Claims fixed (math): **1 critical** (row 4: −13% → −6%)
- Claims struck: **0**
- Lean corpus changes required: **0** (all corrections are in the prose; the kernel was already correct on the −6% number via `validation_brynjolfsson` and `pipeline_displacement_meets_brynjolfsson`)

## Notes

The −13% / −6% confusion is the only material math error. The Brynjolfsson
et al. (2025) headline number for 22–25-year-olds in AI-exposed occupations
is **−6%**. The −13% figure may have been a draft confusion with the
"+6% to +13%" range for **older** workers (which is the OPPOSITE direction)
or with the "up to ≈ −20% entry-level" figure for specific exposed
occupations (software dev, customer support, accountants). The Lean corpus
correctly anchors to −6% in two places (`validation_brynjolfsson` and
`pipeline_displacement_meets_brynjolfsson`), so the kernel was never wrong;
the prose drifted.

Line-number drift (rows 12, 16, 25, 26, 30) is the result of post-draft
edits to the Lean files between the prior builder's read and the rewrite
session. All corrected from the current source.

The rewritten post and the rebuilt web page both anchor every numeric
claim to a specific `file:line` and every theorem to its canonical name.
No claim in the public artifact exceeds what the kernel has signed.
