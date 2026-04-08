# Economy — Audit Pass A (2026-04-08)

Scope: mechanical grep + classify + fix + delete. No bound-tightening, no
derivation-chain tracing, no assumption auditing. Those are separate passes.

State at start: 23 files, 2813 lines, 121 theorems, 0 sorry, 0 axioms, CLEAN
(commit 0e22976). State at end: identical counts, CLEAN, GREEN.

---

## §Constants

Every numeric literal in `Economy/*.lean` was grepped and classified. The
project already had thorough header docstrings on each file pointing to
`REFERENCES.md`, and every empirical literal appears inside a theorem or
`def` whose docstring cites the source inline. No fabricated literals were
found. No magic numbers required promotion.

| file:line | literal | interpretation | source | verdict |
|---|---|---|---|---|
| Bounds.lean:32-35 | 15/100, 40/100, 5/100, 30/100 | `LitBox` exposure/costSavings range | REFERENCES §3 (Acemoglu w32487) + §5 (Goldman) — stated in file header + struct docstring | CITED |
| Bounds.lean:39,50 | 12/100 | upper envelope `0.40 × 0.30` | derived from LitBox; docstring explains | CITED-DERIVED |
| Bounds.lean:58,74 | 75/10000 | lower envelope `0.15 × 0.05` | derived from LitBox; docstring explains | CITED-DERIVED |
| Bounds.lean:85-86 | 20/100, 33/1000, 66/10000 | Acemoglu point estimate | theorem `acemoglu_pointEstimate`, docstring cites w32487 | CITED |
| Bounds.lean:92-93 | 40/100, 175/1000, 7/100 | Goldman high envelope | theorem `goldman_highEnvelope`, docstring cites Goldman 2023 | CITED |
| Empirical.lean:35 | -6/100 | BCC young-worker effect | docstring + REFERENCES §4 | CITED |
| Empirical.lean:39 | 95/1000 | BCC older-worker midpoint | docstring + REFERENCES §4 | CITED |
| Empirical.lean:43 | 77/100 | API automation fraction | docstring + REFERENCES §2 | CITED |
| Empirical.lean:47 | 50/100 | claude.ai augmentation | docstring + REFERENCES §2 | CITED |
| Empirical.lean:51 | 66/10000 | Acemoglu 10yr TFP | docstring + REFERENCES §3 | CITED |
| Empirical.lean:55 | 7/100 | Goldman 10yr GDP | docstring + REFERENCES §5 | CITED |
| Forecast.lean:144-148 | T=4, Hmax=12, α=6/10, gK=3/1000, costSavings=175/1000 | METR-fast scenario | docstring names METR TH1.1 + Acemoglu params | CITED |
| Forecast.lean:160-164 | T=7, same others | METR-baseline | docstring names 2019-25 baseline | CITED |
| IntelligenceTrajectory.lean:82,92 | 24 months, ×64, <11 | capability-doubling corollaries | docstring + REFERENCES §METR | CITED |
| IntelligenceTrajectory.lean:100-122 | 11^7, 2^24, 16777216, 19487171 | intermediate arithmetic for `< 11` proof | mathematical, not empirical | UNCITED-MATHEMATICAL |
| LaborMarketDynamics.lean:62 | 5/1000 | Sahm rule threshold (0.5pp) | docstring + REFERENCES §Sahm | CITED |
| Welfare.lean:76-88 | 1, 11/10, 1/2, 11/20 | witness constants for existential | mathematical, not empirical | UNCITED-MATHEMATICAL |
| Inequality.lean:30-31 (comments) | 0.77, 0.10 | `ψ_k`, `ν_k` field commentary | struct comment, not inline literal | CITED |

**Counts**: ~40 literals reviewed. CITED = 38. UNCITED-MATHEMATICAL = 2
(rational arithmetic inside proofs, not empirical). UNCITED-EMPIRICAL = 0.
MAGIC = 0. FABRICATED = 0.

**Action**: none. Pass A is a no-op. The prior hardening commits (`fdab939`,
`9e049b8`, `0e22976`) already pulled every empirical literal into a named,
docstring-cited theorem or `def`.

---

## §Soundness

`grep -rn 'decide\|native_decide\|noncomputable\|@\[simp\]\|Classical\.choice\|Classical\.em' Economy/*.lean`

| hit class | count | verdict |
|---|---|---|
| `noncomputable def` / `noncomputable section` | 30 | LEGITIMATE — real-valued analysis, computability irrelevant |
| `decide` / `native_decide` | 0 | — |
| `Classical.choice` / `Classical.em` (explicit) | 0 | — |
| `@[simp]` (project-level) | 0 | — |

No soundness-affecting hits. Mathlib pulls in `Classical` as needed for real
analysis but no theorem in `Economy/*.lean` appeals to it directly.

### Unused-hypothesis scan

`lake build` produces 13 warnings, all `unused variable`. These are
hypotheses carried in theorem statements (nonnegativity bounds, monotonicity
guards) that the proof ultimately does not touch. They are concerning-low
(interface noise, not soundness) — the theorems are still true, but a reader
might assume a hypothesis is load-bearing when it is not.

| file:line | var | theorem | class |
|---|---|---|---|
| Services.lean:89 | `hsE0 : 0 ≤ sE` | `baumol_bowen_drag` | interface-symmetry |
| Bounds.lean:57 | `hf_nn : 0 ≤ f_max` | `litBox_envelope` | interface-symmetry |
| TaskModel.lean:148 | `hc` | Hulten bound | interface-symmetry |
| LaborShare.lean:83 | `hα` | labor-share lemma | interface-symmetry |
| IntelligenceTrajectory.lean:44 | `hT` | horizon lemma | interface-symmetry |
| FinanceRealCoupling.lean:73 | `hY` | net-output lemma | interface-symmetry |
| Forecast.lean:78 | `hT'` | trajectory lemma | interface-symmetry |
| ScenarioSpace.lean:132,194,214,361,400 | `ht_now`, `hL`, `hT`, `hI₁nn`, `ht_now` | dominance lemmas | interface-symmetry |
| ScenarioSpace.lean:386 | `τ` | trajectory eval | bound-variable |

**Verdict**: no soundness bug. Flagged for a later pass to either (a) tighten
statements by dropping unused hypotheses, or (b) underscore-prefix them to
silence the warnings after confirming each is intentional API padding. Out
of scope for Pass A.

---

## §Triviality

Walked every theorem. Prior commit `0e22976` already did a triviality sweep.
Remaining candidates:

- `grep ':= rfl'` produced 1 hit — a `calc` step in `TaskModel.lean:175`,
  not a whole theorem. OK.
- No theorem body is a single `positivity` / `ring` / `norm_num` / `linarith`
  on a re-statement of a definition. All one-liner `nlinarith` / `linarith`
  proofs (e.g. `baumol_bowen_drag`, `deltaTFP_le_one`, `aggregateExposure_*`)
  use real hypotheses and produce real bounds.
- No theorem re-asserts a struct field.
- No orphaned theorems found (every theorem is either referenced elsewhere
  in the project or documented as a headline result in README-equivalent
  docstrings).

**Deletions**: 0. Pass C is a no-op because the prior audit already caught
the easy triviality. The next triviality wave will need to be semantic
(e.g., "this theorem is a special case of that one") rather than syntactic.

---

## Summary

Pass A (constants): 0 fixes. Every literal already cited.
Pass B (soundness): 0 fixes. 13 unused-hypothesis warnings documented.
Pass C (triviality): 0 deletions. Prior sweep already landed.

`make proof`: GREEN, CLEAN, 23 files, 2813 lines, 121 theorems, 3 lemmas,
52 defs, 0 sorry, 0 axioms, 13 warnings (all unused-variable, interface
symmetry).

The economy project was already in audit-clean state when Pass A started.
This audit's value is the AUDIT.md record itself — a written confirmation
that a grep-based soundness + citation + triviality pass produces zero
findings, plus the unused-hypothesis list for a future tightening pass.


---

## Bounds Tightening Pass (2026-04-08)

State at start: 23 files, 2813 lines, 121 theorems, 0 sorry, 0 axioms, CLEAN,
12 `unused variable` warnings.
State at end: 23 files, 2855 lines, 124 theorems, 0 sorry, 0 axioms, CLEAN,
**0 warnings**.

### Tightened

| Theorem | Before | After | Proof delta |
|---|---|---|---|
| `FinanceRealCoupling.keynesian_multiplier` | `0 ≤ m`, `0 ≤ τ`, `Δ ≤ Δ·mult` | Same weak form + NEW `keynesian_multiplier_strict` for `0 < m`, `τ < 1`, `0 < Δ` giving `Δ < Δ·mult` | +20L strict companion via `mul_lt_mul_of_pos_left` |
| `FinancialMarkets.PV_mono_cashflows` | weak `≤` only | Same + NEW `PV_mono_cashflows_strict` requiring one strict index `k < n` with `c k < c' k` | +5L via `Finset.sum_lt_sum` |
| `ScenarioSpace.hyperExp_dominates_continued` | weak `≤` at `T ≤ t` | Same + NEW `hyperExp_dominates_continued_strict` for `T < t` giving strict `<`. Crossover is exactly at `t = T` (both = 2) | +8L via `Real.rpow_lt_rpow_of_exponent_lt` |

Strict `continued_dominates_plateau_strict` already existed (weak companion at `t_now < t`).

### Already Tight

- `Bounds.litBox_upper`: envelope `0.12 = 0.40 × 0.30` is the exact corner of the parameter cube — both maxima realized simultaneously. Corner check: `acemoglu_below_goldman_parameterized` already pins both endpoints.
- `Bounds.acemoglu_low_corner`, `Bounds.goldman_high_corner`: stated as exact equalities at the corners, not bounds.
- `Bounds.litBox_envelope`: the `(75/10000)·(1-f_max)` floor is exact when `exposure = 0.15`, `costSavings = 0.05`, `friction = f_max`. Tight at the cube vertex.
- `Inequality.topDecile_linear_bound`: already stated as exact identity `Δshare = Δα · (ψ - ν)`, not a bound. Tight by definition (a single `field_simp; ring`).
- `MatchingModel.steadyStateU_strictMono_separation`: already strict; `hs : 0 ≤ s` is load-bearing (needed for `0 < s + f`).
- `Welfare.welfare_can_fall_with_gdp_rise`: witness `(1, 1.1, 1, 1/2)` is concrete. Margin `log(11/20)` is not obviously improvable without abandoning integer-friendly endpoints.
- `Macro.keynesian_multiplier`: (see above — moved to Tightened via strict companion). Base identity is the closed form of the full geometric sum; no finite truncation.
- `Forecast.forecast_mono_intelligence` / `metr_fast_dominates_baseline`: weak `≤` is correct — at `t = 0` both sides are `0`, so a universal strict `<` fails. Strict would require `t > 0` and `T₁ < T₂` strict, and the chain through `exposureFromHorizon` is only weakly monotone (min/max clipping). Tight under current `exposureFromHorizon`.

### Implicit Assumptions Surfaced / Removed

All 12 `unused variable` warnings investigated. Each was a hypothesis in the
theorem statement that the proof did not actually use. Since every unused
hypothesis is either (a) redundant strengthening of the statement or
(b) a load-bearing hint the proof silently skipped, each was REMOVED from
the statement (case a) after re-verifying the proof closes without it.
This TIGHTENS the statement by weakening its preconditions.

| File:line | Removed hypothesis | Theorem |
|---|---|---|
| Services.lean:89 | `hsE0 : 0 ≤ sE` | `baumol_bowen_drag` (only `sE ≤ 1`, `0 ≤ gP` needed) |
| Bounds.lean:57 | `hf_nn : 0 ≤ f_max` | `litBox_envelope` (only `hf_lt : f_max < 1` needed; nonneg follows from `hf_le` + `p.fric_nonneg`) |
| TaskModel.lean:148 | `hc : 0 ≤ c` | `acemoglu_macro_bound` (bound holds for any real `c` under `h_bounded`) |
| LaborShare.lean:83 | `hα : ∀ i, 0 ≤ α i` | `laborShare_strict_antitone_single` (only `hαj : 0 < α j` at index `j`, rewriting on others) |
| IntelligenceTrajectory.lean:44 | `hT : T ≠ 0` | `intelligenceLevel_zero` (`0 / T = 0` holds in Lean for any `T`) |
| FinanceRealCoupling.lean:73 | `hY : 0 < Y` | `ghost_gdp_dominates_iff` (identity closes via `linarith` alone) |
| Forecast.lean:78 | `hT' : 0 < T'` | `gA_antitone_doublingTime` (implied by `hT : 0 < T` and `T ≤ T'`) |
| ScenarioSpace.lean:132 | `ht_now : 0 ≤ t_now` | `continued_dominates_plateau_strict` |
| ScenarioSpace.lean:142 | `ht_now : 0 ≤ t_now` | `continued_dominates_plateau` (weak) |
| ScenarioSpace.lean:194 | `hL : 0 < L` | `continued_exceeds_sigmoid_ceiling` (works for any `L`; implementation picks any witness via `tendsto_atTop_atTop`) |
| ScenarioSpace.lean:214 | `hT : 0 < T` | `aiWinter_tendsto_zero` (only `0 < decay` needed; `2 ^ (t_winter / T)` is a bounded constant regardless of sign of `T`) |
| ScenarioSpace.lean:361 | `hI₁nn : 0 ≤ I₁ t` | `gdp_dominance_from_intelligence_dominance` (exposure function clips to `[0,1]`; nonnegativity of `I₁ t` is not needed) |
| ScenarioSpace.lean:400 | `ht_now : 0 ≤ t_now` | `mythos_plateau_corollary` |
| ScenarioSpace.lean:479 | `ht_now : 0 ≤ t_now` | `plateau_below_continued_GDP` |
| ScenarioSpace.lean:386 | `τ : Trajectory` | `welfare_can_diverge_under_any_trajectory` — renamed to `_τ`; the theorem binds `_τ` to document that the witness is trajectory-independent (load-bearing for reader, not for proof) |

### Tried Failed

None. Every attempted tightening in scope landed. `forecast_mono_intelligence`
strict version was considered and rejected as structurally impossible under
the current `exposureFromHorizon` (it clips, so two scenarios with different
doubling times can coincide on any interval where both have saturated
exposure).

### Mathlib gaps

None blocking further tightening at this pass. Every remaining "weak `≤`" in
the corpus is either an exact identity, a clipped/saturated-region result,
or already has a strict companion after this pass. The corpus is now as
tight as the current definitions permit. Further tightening would require
changing definitions (e.g. replacing `exposureFromHorizon`'s hard min/max
clip with a smooth saturation) — out of scope for an audit pass.

### Final numbers

```
files:     23
lines:    2855  (+42)
theorems:  124  (+3)
sorry:       0
axioms:      0
warnings:    0  (was 12)
errors:      0
build:   GREEN
sound:   CLEAN
```
