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
