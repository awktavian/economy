# References — `economy`

All empirical parameters in the Lean formalization come from the five sources below. Numbers are quoted verbatim; no number in the Lean files exceeds what a source directly states.

## 1. Claude Mythos Preview System Card (Anthropic, 2026-04-07)

- **93.9%** SWE-bench Verified
- **77.8%** SWE-bench Pro
- **82%** Terminal-Bench 2.0
- **97.6%** USAMO 2026
- Prohibited-method rate: **< 0.001%**
- Availability: limited preview (AWS, Apple, Google, JPMorganChase, Microsoft, NVIDIA — cybersecurity use)
- URL: https://www.anthropic.com/claude-mythos-preview-risk-report (+ AWS Bedrock model card)

## 2. Anthropic Economic Index — March 2026 ("Learning curves") and January 2026 ("Economic primitives")

- API traffic: **77% automation / 12% augmentation**
- Claude.ai traffic: approximately 50/50, augmentation slightly over half
- URLs:
  - https://www.anthropic.com/research/economic-index-march-2026-report
  - https://www.anthropic.com/research/anthropic-economic-index-january-2026-report

## 3. Acemoglu (2024), "The Simple Macroeconomics of AI" — NBER Working Paper 32487

- Core result (Hulten's theorem): **ΔTFP ≤ exposureShare × avgCostSavings**
- Point estimate: **≤ 0.66% total TFP increase over 10 years**
- URL: https://www.nber.org/papers/w32487

## 4. Brynjolfsson, Chandar, Chen (2025), "Canaries in the Coal Mine" — Stanford Digital Economy Lab

- Data: ADP payroll microdata, late 2022 – July 2025
- **−6% employment for 22–25-year-olds in high-AI-exposure jobs**
- **+6% to +13%** for workers aged 30+ in the same jobs
- Up to **≈ −20% entry-level** in specific exposed occupations (software dev, customer support, accountants)
- URL: https://digitaleconomy.stanford.edu/wp-content/uploads/2025/08/Canaries_BrynjolfssonChandarChen.pdf

## 5. Alternative high estimates (sensitivity bounds only)

- **Goldman Sachs (2023)**: ~1.5% annual productivity growth boost; ~7% (~$7T) global GDP increase over 10 years.
- **IMF (Jan 2024), "Gen-AI and the Future of Work"**: ~40% global employment exposure; ~60% in advanced economies.

These are cited as the HIGH end of the sensitivity envelope in `Economy/Bounds.lean`. They are NOT treated as point estimates; the Acemoglu 0.66% figure is the conservative anchor.
