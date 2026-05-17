# CLAUDE.md — guide for AI assistants working on the economy corpus

This is the repository behind [tim.awkronos.com/economy](https://tim.awkronos.com/economy). It is a Lean 4 + Mathlib formalization of a small macroeconomic model: Cobb-Douglas production, CES substitution, a scenario lattice over growth shapes, and a welfare/inequality layer, plus three failure-mode modules (job-swapping, recession, capex bubble).

The README is for humans arriving from the blog post. This file is for you.

## The invariant

**Zero sorry. Zero user-defined axioms. Every theorem kernel-clean under `[propext, Classical.choice, Quot.sound]`.** If any change to this repo violates that, back it out before you commit. The entire point of the project is that the receipts on the blog are real — breaking kernel cleanliness silently is the worst possible failure mode.

Before committing anything, run:

```bash
make proof
```

and verify that the output shows `sorry: 0   axioms: 0   build: GREEN   sound: CLEAN`. If it doesn\'t, you have work to do.

## The toolchain

- Lean 4 (`lean-4.30.0-rc1`) + Mathlib, pinned via `lean-toolchain` and `lake-manifest.json`.
- `lake build economy` for a full build (~12s cached, ~45s cold).
- `lake env lean Economy/Foo.lean` for single-file type-check (~7s). Use this for iteration. Never run a full `lake build` in the middle of a proof exploration.
- `make proof` for the canonical build + report used by the daemon, the blog footer, and the statusline.

## Editing .lean files

**Use Python file I/O, not the Edit or Write tool.** Claude Code\'s diagnostic system auto-modifies .lean files between tool calls, which corrupts multi-hunk edits. The canonical pattern:

```python
p = "Economy/Foo.lean"
s = open(p).read()
s = s.replace(OLD, NEW)
open(p, "w").write(s)
```

Then immediately verify with `lake env lean Economy/Foo.lean 2>&1 | tail -20`. Write + verify in one shell command so the linter has no window to interfere.

## The hard rules

1. **No `axiom` keyword.** If you need to assume something, use `theorem name : T := by sorry` and leave a comment explaining what would close it. Sorry exposes the goal; axiom hides it.

2. **No TN placeholders.** `:= True`, `:= PUnit`, `:= 0`, `:= ⊥`, `:= trivial` on target positions are banned. They compile but prove nothing. If you see one, replace it with a real mathematical statement and a `sorry` if needed.

3. **No inflation.** Theorems like `(N : ℕ) = N := rfl` are banned. So is defining a structure with field `x := 5` and then writing `theorem foo : struct.x = 5 := rfl`. If removing the theorem changes nothing downstream, delete it.

4. **Tier discipline.** Every file opens with a tier label (THEOREM / FRAMEWORK / NUMERICAL OBSERVATION). Never state a framework claim as a theorem. Never cite an observation as if it were proved from first principles.

5. **Truth-check before proving.** If you\'re stuck on a sorry for more than about 30 minutes, the statement might be false. Substitute concrete numbers. Check the limit as any parameter approaches its boundary. A sorry on a false statement wastes all downstream work.

6. **No `decide` or `native_decide` on real-valued goals.** `decide` is for `Decidable` props. Real-valued arithmetic needs `norm_num`, `nlinarith`, `positivity`, `linarith`, `field_simp`, or `ring`.

## The seven-module spine

| Module | Role | Load-bearing theorems |
|---|---|---|
| `Calibration` | entry point, three canonical parameter sets | V1-V6 validation theorems |
| `TaskModel` | Cobb-Douglas foundation + Hulten | `log_Y_eq`, `hulten_discrete`, `acemoglu_macro_bound` |
| `CES` | elasticity of substitution | `ces_to_cobb_douglas_limit`, `sigmoidToRho_pos_iff` |
| `IntelligenceTrajectory` | growth shapes | `intelligenceLevel_strictMono`, `intelligenceLevel_from_slope` |
| `Macro` | Solow + Ghost GDP + factor income | `ghost_gdp_constant_labor`, `factor_income_exhausts` |
| `ScenarioSpace` | five-trajectory dominance lattice | `gdp_dominance_from_intelligence_dominance`, `welfare_can_diverge_under_any_trajectory` |
| `EndToEndForecast` | composition tests | `pipeline_metr_horizon_36mo` and four siblings |

Plus three hardened failure-mode modules:

- `JobSwapping` — CES nest over `(capital + AI substitutes)` and `non-substitutable labor`. Keystone: `jobSwap_cobbDouglas_zero_Lnon_limit`.
- `RecessionShock` — Poisson regime switching. Keystone: `recession_expected_loss`.
- `CapexBubble` — debt sustainability switch. Keystone: `bubble_pop_ghost_gdp_loss`.

## How the blog footer is computed

The blog at tim.awkronos.com/economy displays `202 theorems, 0 sorry, 0 axioms, commit 54077a1` in its footer. That number comes directly from `/tmp/proof-report.json`, which is written by `make proof`. If you change the corpus, `make proof` updates that file, and the blog footer must be kept in sync via the hand-edited HTML (`~/tim/web/economy/index.html` has a hardcoded theorem count in the footer).

When you add theorems, update the footer count. When you delete them, update the footer count. When you bump the commit, update the commit hash. The receipt is load-bearing; don\'t let it go stale.

## Common tasks

**Adding a new empirical anchor.** Put the number in `Economy/Empirical.lean` as a named `def` with a docstring citing the source. Cross-reference in `REFERENCES.md`. Do not inline literal numbers in proofs — always go through the named def.

**Adding a new theorem.** Put it in the smallest existing module that makes sense. Name it so the blog can cite it as `Module.theorem_name`. Open with a one-line docstring describing what it says economically. Close with `#print axioms theorem_name` in a comment at the top of the module if it\'s a headline theorem — that\'s the audit trail.

**Changing a calibration.** Edit `Economy/Calibration.lean`. The subtype constraints will catch out-of-range values at compile time. Re-run V1-V6 validations to confirm the sanity checks still hold.

**Closing a sorry.** Sorries shouldn\'t exist in this repo, but if one gets introduced in a WIP branch, attack it in this order: (a) does the statement parse correctly, (b) is it true numerically at concrete values, (c) does a Mathlib one-liner close it, (d) does decomposition into sub-lemmas expose the blocker. If none of those work, the statement is probably too strong and should be weakened.

## What not to do

- Do not introduce Mathlib dependencies you can\'t justify. The corpus is deliberately lightweight.
- Do not add `@[simp]` attributes. Every use of `simp` in this repo is scoped with `simp only [...]` listing the lemmas explicitly.
- Do not use `omega` on goals over ℝ. It only handles ℕ and ℤ.
- Do not paper over a regression. If a change breaks a theorem, figure out what broke and why. Don\'t just wrap the theorem in a weaker statement to make it compile.
- Do not commit a broken build. Ever. The statusline and the blog both key off `make proof` output.

## The author\'s note

This is a small corpus with a focused goal. It is not trying to be a complete DSGE model, a macroeconometric forecast, or an AI safety framework. It is trying to show that a small number of structural claims about the current US economy are self-consistent and can be stated precisely enough to be machine-checked.

Everything here is in service of that one claim. When you work on this corpus, ask: *does this change make the math clearer, the claims stronger, or the receipts more honest?* If not, don\'t make the change.

And always, before you commit:

```bash
make proof
```

Green build. Zero sorry. Zero axiom. Kernel clean.

That is the whole deal.
