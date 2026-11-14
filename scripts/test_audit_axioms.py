#!/usr/bin/env python3
"""Tests for scripts/audit_axioms.py — the economy soundness gate.

Everything here runs without Lean. The kernel path is exercised against a
`lake` shim that echoes canned `#print axioms` output, so the batching,
command construction and parsing are pinned even on a machine with no
toolchain. One test does touch the real corpus: the static claim (no sorry,
no native_decide, no user axioms, README census pinned) must hold at HEAD.
"""

import json
import os
import subprocess
import sys
import tempfile
import unittest

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, SCRIPT_DIR)

import audit_axioms as A  # noqa: E402

REPO_ROOT = os.path.dirname(SCRIPT_DIR)

# The unit suite must never queue on the host's real slot table: it checks
# command construction, not admission. BuildSlotLease below exercises the
# lease itself against a fake adapter, which is an explicit `script=` and so
# is unaffected by this switch.
os.environ["ECONOMY_AUDIT_NO_SLOT"] = "1"


def write(path, text):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w", encoding="utf-8") as fh:
        fh.write(text)
    return path


# --------------------------------------------------------------------------
# Stripping
# --------------------------------------------------------------------------


class StripComments(unittest.TestCase):

    def test_offsets_are_preserved(self):
        src = "theorem a : True := by\n  /- block -/\n  sorry -- trailing\n"
        out = A.strip_comments(src)
        self.assertEqual(len(out), len(src))
        self.assertEqual([i for i, ch in enumerate(out) if ch == "\n"],
                         [i for i, ch in enumerate(src) if ch == "\n"])

    def test_line_comment_is_blanked(self):
        out = A.strip_comments("theorem foo : T := by\n  exact bar -- sorry here\n")
        self.assertNotIn("sorry", out)

    def test_doc_comment_is_blanked(self):
        out = A.strip_comments("/-- This proves no sorry is used. -/\ntheorem foo : T\n")
        self.assertNotIn("sorry", out)

    def test_nested_block_comments(self):
        src = "/- outer /- inner sorry -/ still comment -/\ntheorem real : T := sorry\n"
        out = A.strip_comments(src)
        self.assertEqual(out.count("sorry"), 1)

    def test_sorry_inside_string_is_not_code(self):
        out = A.strip_comments('#eval "sorry"\ntheorem foo : T := sorry\n')
        self.assertEqual(out.count("sorry"), 1)

    def test_raw_string_with_hash_delimiters(self):
        out = A.strip_comments('def s := #"sorry inside"#\ntheorem foo : T := sorry\n')
        self.assertEqual(out.count("sorry"), 1)

    def test_apostrophe_in_line_comment_does_not_swallow_code(self):
        # `don't` inside a comment must not open a char literal that hides the
        # real sorry on the next line.
        src = "-- don't panic\ntheorem foo : T := sorry\n"
        out = A.strip_comments(src)
        self.assertIn("sorry", out)


class TokenBoundary(unittest.TestCase):

    def test_substring_is_not_a_hit(self):
        self.assertEqual(A.token_hits("lemma sorry_ax_used : True := trivial", "sorry"), [])
        self.assertEqual(A.token_hits("def sorryNot : Nat := 1", "sorry"), [])

    def test_native_decide_is_not_double_counted_as_decide(self):
        line = "by native_decide"
        self.assertEqual(len(A.token_hits(line, "native_decide")), 1)
        # the `_` before `decide` is an identifier character, so the bare
        # `decide` scan cannot report the tail of `native_decide`
        self.assertEqual(A.token_hits(line, "decide"), [])

    def test_bare_decide_and_sorryax_boundaries(self):
        self.assertEqual(len(A.token_hits("by decide", "decide")), 1)
        self.assertEqual(A.token_hits("Term sorryAx Nat", "sorry"), [])


# --------------------------------------------------------------------------
# Declaration scanning
# --------------------------------------------------------------------------


class ScanSource(unittest.TestCase):

    def scan(self, src):
        return A.scan_source("Economy/Foo.lean", src)[0]

    def test_namespace_stack_builds_full_names(self):
        src = (
            "namespace Economy\n"
            "namespace SolowGrowth\n"
            "theorem ghost : True := trivial\n"
            "end SolowGrowth\n"
            "theorem outer : True := trivial\n"
            "end Economy\n"
        )
        decls = self.scan(src).decls
        self.assertEqual([d.full for d in decls],
                         ["Economy.SolowGrowth.ghost", "Economy.outer"])

    def test_binders_and_unicode_do_not_leak_into_names(self):
        src = "namespace Economy\ntheorem foo {α : Type} (h : 0 < (1:ℝ)) : T := by\n  linarith\nend Economy\n"
        decls = self.scan(src).decls
        self.assertEqual(decls[0].full, "Economy.foo")

    def test_protected_and_private_modifiers(self):
        src = ("private lemma hid : True := trivial\n"
               "protected theorem vis : True := trivial\n"
               "noncomputable def f : Nat := 1\n")
        decls = self.scan(src).decls
        self.assertEqual([d.private for d in decls], [True, False, False])
        self.assertEqual([d.kind for d in decls], ["lemma", "theorem", "def"])

    def test_instance_without_name_is_counted_not_named(self):
        decls = self.scan("instance : Coe Nat Int := ⟨Int.ofNat⟩\n").decls
        self.assertEqual(len(decls), 1)
        self.assertEqual(decls[0].full, "")

    def test_commented_out_theorem_is_not_in_the_census(self):
        decls = self.scan("-- theorem gone : True := trivial\n/- theorem also : T := sorry -/\n").decls
        self.assertEqual(decls, [])

    def test_sorry_in_code_is_found_with_line_number(self):
        s = self.scan("theorem a : T := by\n  sorry\n")
        self.assertEqual(s.sorry, [2])

    def test_sorry_only_in_docstring_is_not_found(self):
        s = self.scan("/-- formerly a sorry, now proved -/\ntheorem a : T := trivial\n")
        self.assertEqual(s.sorry, [])

    def test_native_decide_and_bare_decide_are_separated(self):
        s = self.scan("theorem a : T := by native_decide\ntheorem b : T := by decide\n")
        self.assertEqual(s.native_decide, [1])
        self.assertEqual(s.decide, [2])

    def test_user_axiom_is_recorded(self):
        s = self.scan("axiom myAssumption : T\n")
        self.assertEqual(s.axioms, [("myAssumption", 1)])

    def test_axiom_word_in_prose_is_not_a_declaration(self):
        s = self.scan("/-- no axiom here -/\ntheorem a : T := trivial\n")
        self.assertEqual(s.axioms, [])

    def test_placeholder_body_on_theorem_is_flagged(self):
        s = self.scan("theorem a : P := True\ntheorem b : Q := by trivial\n")
        self.assertEqual(s.placeholders, [1])

    def test_placeholder_body_on_def_is_not_flagged(self):
        s = self.scan("def marker : Prop := True\n").decls
        self.assertEqual(s[0].kind, "def")
        self.assertEqual(self.scan("def marker : Prop := True\n").placeholders, [])

    def test_placeholder_body_on_the_next_line_is_still_flagged(self):
        s = self.scan("theorem a : P :=\n  trivial\n")
        self.assertEqual(s.placeholders, [2])

    def test_real_constructor_body_is_not_a_placeholder(self):
        s = self.scan("theorem a : True := True.intro\ntheorem b : T := by\n  exact foo\n")
        self.assertEqual(s.placeholders, [])

    def test_print_axioms_in_source_is_counted(self):
        s = self.scan("theorem a : T := trivial\n#print axioms a\n")
        self.assertEqual(s.print_axioms, 1)


# --------------------------------------------------------------------------
# Fixture repository
# --------------------------------------------------------------------------

CLEAN_MODULE = """namespace Economy
namespace Sub

/-- Cited by the README. -/
theorem headline_result (h : 0 < (1 : Nat)) : 0 < 1 := Nat.succ_pos 0

private lemma helper_thing : 1 < 2 := by decide

end Sub
end Economy
"""

OTHER_MODULE = """namespace Economy

theorem second_result : 0 = 0 := rfl

def calExample2026 : Nat := 3

end Economy
"""


def census_block(**over):
    vals = {
        "lean_files": 2,
        "theorem_count": 2,
        "lemma_count": 1,
        "other_decl_count": 1,
        "private_decls": 1,
        "public_kernel_decls": 2,
        "sorry_in_code": 0,
        "native_decide_in_code": 0,
        "user_axioms": 0,
        "placeholders": 0,
        "theorem_citations": 2,
        "allowed_axioms": "propext, Classical.choice, Quot.sound",
    }
    vals.update(over)
    lines = ["# %s" % A.CENSUS_BEGIN]
    lines += ["%s: %s" % (k, vals[k]) for k in A.CENSUS_KEYS]
    lines.append("# %s" % A.CENSUS_END)
    return "\n".join(lines)


def good_ci():
    return """name: CI
on: [push]
jobs:
  soundness:
    runs-on: [self-hosted, lean]
    timeout-minutes: 45
    steps:
      - uses: actions/checkout@v4
        with:
          persist-credentials: false
      - name: Build and gate
        shell: bash
        run: |
          set -euo pipefail
          lake build Economy
          python3 scripts/audit_axioms.py --check --verify-kernel --slot-wait 900
"""


class Fixture(unittest.TestCase):
    """A miniature repo the gates can be pointed at."""

    def setUp(self):
        self.tmp = tempfile.mkdtemp(prefix="audit-fixture-")
        self.root = self.tmp
        write(os.path.join(self.root, "Economy", "Foo.lean"), CLEAN_MODULE)
        write(os.path.join(self.root, "Economy", "Bar.lean"), OTHER_MODULE)
        self.readme = (
            "# economy\n\n"
            "| Blog claim | Theorem | File |\n"
            "|---|---|---|\n"
            "| \"headline\" | `Economy.Sub.headline_result` | [`Economy/Foo.lean`](x) |\n"
            "| \"second\" | `second_result` | [`Economy/Bar.lean`](x) |\n\n"
            "```text\n" + census_block() + "\n```\n"
        )
        write(os.path.join(self.root, "README.md"), self.readme)
        write(os.path.join(self.root, ".github", "workflows", "ci.yml"), good_ci())

    def tearDown(self):
        import shutil
        shutil.rmtree(self.tmp, ignore_errors=True)

    def census(self):
        return A.census(self.root)


class CensusOnFixture(Fixture):

    def test_counts(self):
        c = self.census()
        self.assertEqual(c["counts"], {
            "lean_files": 2,
            "theorem_count": 2,
            "lemma_count": 1,
            "other_decl_count": 1,
            "private_decls": 1,
            "public_kernel_decls": 2,
            "sorry_in_code": 0,
            "native_decide_in_code": 0,
            "user_axioms": 0,
            "placeholders": 0,
        })

    def test_public_kernel_list_skips_privates(self):
        self.assertEqual(sorted(d.full for d in self.census()["public_kernel"]),
                         ["Economy.Sub.headline_result", "Economy.second_result"])

    def test_fixture_readme_is_pinned(self):
        self.assertEqual(A.readme_violations(self.root, self.census()), [])

    def test_fixture_ci_is_clean(self):
        self.assertEqual(A.ci_violations(self.root), [])

    def test_dotted_and_leaf_citations_both_resolve(self):
        c = self.census()
        universe = A.citation_universe(c)
        fulls = sorted({d.full for d in c["decls"] if d.full})
        self.assertTrue(A.citation_resolves("Economy.Sub.headline_result", universe, fulls))
        self.assertTrue(A.citation_resolves("second_result", universe, fulls))
        self.assertFalse(A.citation_resolves("Economy.Sub.not_there_result", universe, fulls))
        # a wrong namespace prefix on a real leaf is not a receipt
        self.assertFalse(A.citation_resolves("Economy.Wrong.second_result", universe, fulls))


class StaleClaims(Fixture):

    def test_missing_census_block_is_reported(self):
        text = "# economy\n\nZero sorry, zero axioms, trust us.\n"
        v = A.readme_violations(self.root, self.census(), readme_text=text)
        self.assertEqual(len(v), 1)
        self.assertIn("audit-census:begin", v[0])

    def test_stale_theorem_count_is_reported(self):
        c = self.census()
        text = self.readme.replace("theorem_count: 2", "theorem_count: 47")
        v = A.readme_violations(self.root, c, readme_text=text)
        self.assertTrue(any("theorem_count" in item and "47" in item for item in v), v)

    def test_missing_key_is_reported(self):
        text = self.readme.replace("native_decide_in_code: 0\n", "")
        v = A.readme_violations(self.root, self.census(), readme_text=text)
        self.assertTrue(any("native_decide_in_code" in item for item in v), v)

    def test_unknown_key_is_reported(self):
        text = self.readme.replace("# " + A.CENSUS_END,
                                   "made_up_count: 9\n# %s" % A.CENSUS_END)
        v = A.readme_violations(self.root, self.census(), readme_text=text)
        self.assertTrue(any("made_up_count" in item for item in v), v)

    def test_deleted_cited_theorem_is_reported(self):
        c = self.census()
        os.remove(os.path.join(self.root, "Economy", "Bar.lean"))
        c2 = A.census(self.root)
        self.assertEqual(c["counts"]["lean_files"], 2)
        v = A.readme_violations(self.root, c2)
        self.assertTrue(any("second_result" in item for item in v), v)

    def test_introduced_sorry_is_a_static_violation(self):
        write(os.path.join(self.root, "Economy", "Bad.lean"),
              "namespace Economy\ntheorem regressed : True := by\n  sorry\nend Economy\n")
        c = A.census(self.root)
        v = A.static_violations(self.root, c)
        self.assertTrue(any("`sorry` in executable code" in item and ":3:" in item for item in v), v)
        self.assertEqual(c["counts"]["sorry_in_code"], 1)
        self.assertTrue(any("sorry_in_code" in item for item in
                            A.readme_violations(self.root, c)), A.readme_violations(self.root, c))

    def test_introduced_axiom_is_a_static_violation(self):
        write(os.path.join(self.root, "Economy", "Bad.lean"),
              "namespace Economy\naxiom assumed_pricethis : True\nend Economy\n")
        v = A.static_violations(self.root, A.census(self.root))
        self.assertTrue(any("user `axiom` declaration" in item for item in v), v)

    def test_empty_corpus_is_not_certified(self):
        empty = tempfile.mkdtemp(prefix="audit-empty-")
        try:
            v = A.static_violations(empty, A.census(empty))
            self.assertTrue(any("would be certifying nothing" in item for item in v), v)
        finally:
            import shutil
            shutil.rmtree(empty, ignore_errors=True)


class CiInvariants(Fixture):

    def ci(self, text):
        return A.ci_violations(self.root, text=text)

    def test_gate_not_wired(self):
        self.assertTrue(any("never runs in CI" in v for v in self.ci("name: CI\nrun: lake build\n")))

    def test_kernel_mode_required(self):
        text = good_ci().replace("--check --verify-kernel", "--check")
        self.assertTrue(any("--verify-kernel" in v for v in self.ci(text)), self.ci(text))

    def test_destructive_cache_rm_is_refused(self):
        text = good_ci().replace("          python3 scripts",
                                 "          rm -rf \"$HOME/.lean-cache-ci\"\n          python3 scripts")
        self.assertTrue(any("destructive cache command" in v for v in self.ci(text)), self.ci(text))

    def test_or_true_swallows_failure(self):
        text = good_ci().replace("--verify-kernel", "--verify-kernel || true")
        self.assertTrue(any("|| true" in v for v in self.ci(text)), self.ci(text))

    def test_continue_on_error_is_refused(self):
        text = good_ci().replace("      - name: Build and gate",
                                 "      - name: Build and gate\n        continue-on-error: true")
        self.assertTrue(any("continue-on-error" in v for v in self.ci(text)), self.ci(text))

    def test_unguarded_cache_get_is_refused(self):
        text = good_ci().replace("          python3 scripts",
                                 "          lake exe cache get\n          python3 scripts")
        self.assertTrue(any("symlink preflight" in v for v in self.ci(text)), self.ci(text))

    def test_symlink_guarded_cache_get_passes(self):
        text = good_ci().replace(
            "          python3 scripts",
            "          LINKED=0\n"
            "          for d in .lake/packages/*; do\n"
            "            if [ -L \"$d\" ]; then LINKED=1; fi\n"
            "          done\n"
            "          if [ \"$LINKED\" = 0 ]; then lake exe cache get; fi\n"
            "          python3 scripts")
        self.assertEqual(self.ci(text), [])

    def test_cache_get_mentioned_in_a_comment_is_not_a_call(self):
        text = good_ci().replace(
            "      - name: Build and gate",
            "      - name: Explain\n        shell: bash\n        run: |\n"
            "          set -euo pipefail\n"
            "          # lake exe cache get would write through a symlinked prefix\n"
            "      - name: Build and gate")
        self.assertEqual(self.ci(text), [])

    def test_missing_persist_credentials(self):
        text = good_ci().replace("          persist-credentials: false\n", "")
        self.assertTrue(any("persist credentials" in v for v in self.ci(text)), self.ci(text))

    def test_multi_line_step_without_pipefail(self):
        text = good_ci().replace("          set -euo pipefail\n", "")
        self.assertTrue(any("set -euo pipefail" in v for v in self.ci(text)), self.ci(text))

    def test_single_line_step_needs_no_pipefail(self):
        text = "name: CI\njobs:\n  a:\n    runs-on: [self-hosted, lean]\n    timeout-minutes: 5\n" \
               "    steps:\n      - run: python3 scripts/audit_axioms.py --check --verify-kernel --no-slot\n" \
               "      - uses: actions/checkout@v4\n        with:\n          persist-credentials: false\n"
        self.assertEqual(self.ci(text), [])

    def test_slot_stance_is_required(self):
        # Without a stance a busy host turns the kernel gate red for queueing
        # (rc=75 refusal), and the refusal is not a soundness violation.
        text = good_ci().replace(" --slot-wait 900", "")
        self.assertTrue(any("no stance on the build slot" in v for v in self.ci(text)),
                        self.ci(text))

    def test_no_slot_is_a_stance_too(self):
        text = good_ci().replace(" --slot-wait 900", " --no-slot")
        self.assertEqual(self.ci(text), [])

    def test_backticks_in_a_quoted_echo_are_refused(self):
        # `echo "Skipping `lake exe cache get`..."` looks like a message and is
        # a command substitution: the guarded call runs inside the skip branch.
        text = good_ci().replace(
            "          python3 scripts",
            "          echo \"Skipping `lake exe cache get`: read-only\"\n"
            "          python3 scripts")
        self.assertTrue(any("execute as a command" in v for v in self.ci(text)),
                        self.ci(text))

    def test_lean_action_is_refused(self):
        # The cache call is inside the action, so the file's own preflight
        # cannot cover it, and the runner cannot see the symlink it writes
        # through. This is what cancelled run 43527300771 at 30 minutes.
        text = good_ci() + "      - uses: leanprover/lean-action@v1\n"
        self.assertTrue(any("leanprover/lean-action" in v for v in self.ci(text)),
                        self.ci(text))

    def test_lean_action_named_only_in_a_comment_is_not_a_call(self):
        text = good_ci().replace(
            "      - name: Build and gate",
            "      # leanprover/lean-action would seed the cache unguarded\n"
            "      - name: Build and gate")
        self.assertEqual(self.ci(text), [])

    def test_a_retry_on_a_non_gate_command_is_not_a_swallowed_verdict(self):
        # `|| true` is a defect when it guards a verdict. On a `git fetch`
        # before a read from another repo's object store it is just a retry,
        # and refusing it here would make this gate red over a sibling lane's
        # step that cannot hide a soundness failure.
        text = good_ci().replace(
            "          python3 scripts",
            "          git -C \"$HOME/reality\" fetch -q origin main 2>/dev/null || true\n"
            "          python3 scripts")
        self.assertEqual(self.ci(text), [])

    def test_a_non_gate_step_may_skip_pipefail(self):
        text = good_ci().replace(
            "      - name: Build and gate",
            "      - name: Report\n        shell: bash\n        run: |\n"
            "          set -u\n          echo built\n"
            "      - name: Build and gate")
        self.assertEqual(self.ci(text), [])

    def test_sibling_ratchet_job_coexists(self):
        """The native-trust ratchet job that landed on main beside this gate."""
        sibling = """      - name: Native-trust census ratchet
        shell: bash
        run: |
          set -euo pipefail
          R="${REALITY_CHECKOUT:-$HOME/reality}"
          CENSUS="${RUNNER_TEMP:-/tmp}/native_decide_census.py"
          git -C "$R" fetch -q origin main 2>/dev/null || true
          if git -C "$R" show origin/main:scripts/native_decide_census.py > "$CENSUS" 2>/dev/null \\
              && grep -q -- '--ratchet' "$CENSUS"; then
            python3 "$CENSUS" --self-test
            python3 "$CENSUS" --root "$GITHUB_WORKSPACE" --ratchet baseline.json
            exit "${PIPESTATUS[0]}"
          else
            echo "::warning::census UNMEASURED on this runner"
          fi
"""
        text = good_ci().replace("      - name: Build and gate",
                                 sibling + "      - name: Build and gate")
        self.assertEqual(self.ci(text), [])


# --------------------------------------------------------------------------
# Kernel output handling
# --------------------------------------------------------------------------


class ProbeParsing(unittest.TestCase):

    def test_axiom_list_line(self):
        out = "Economy.foo depends on axioms: [propext, Classical.choice, Quot.sound]\n"
        found, unknown, errors = A.parse_probe_output(out)
        self.assertEqual(found, {"Economy.foo": ["propext", "Classical.choice", "Quot.sound"]})
        self.assertEqual((unknown, errors), ([], []))

    def test_quoted_name_line_matches_the_435_compiler_format(self):
        out = "'Economy.foo' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
        found, _u, _e = A.parse_probe_output(out)
        self.assertEqual(list(found), ["Economy.foo"])

    def test_quoted_no_axiom_line(self):
        out = "'Economy.bar' does not depend on any axioms\n"
        found, _u, _e = A.parse_probe_output(out)
        self.assertEqual(found, {"Economy.bar": []})

    def test_single_axiom_line(self):
        found, _u, _e = A.parse_probe_output("'Economy.baz' depends on axioms: [propext]\n")
        self.assertEqual(found, {"Economy.baz": ["propext"]})

    def test_no_axiom_line(self):
        found, _u, _e = A.parse_probe_output("Economy.bar does not depend on any axioms\n")
        self.assertEqual(found, {"Economy.bar": []})

    def test_sorryax_line(self):
        found, _u, _e = A.parse_probe_output("Economy.bad depends on axioms: [sorryAx]\n")
        self.assertEqual(found["Economy.bad"], ["sorryAx"])

    def test_unknown_identifier_line(self):
        out = ("Economy/Probe.lean:3:0: error: unknown identifier 'Economy.gone'\n"
               "Economy.still depends on axioms: [propext]\n")
        found, unknown, errors = A.parse_probe_output(out)
        self.assertEqual(unknown, ["Economy.gone"])
        self.assertEqual(list(found), ["Economy.still"])
        self.assertEqual(errors, [])

    def test_unicode_and_qualified_names(self):
        out = "Economy.Sub.lemma₁ depends on axioms: [propext]\n"
        found, _u, _e = A.parse_probe_output(out)
        self.assertEqual(list(found), ["Economy.Sub.lemma₁"])

    def test_probe_source_is_a_plain_lean_file(self):
        src = A.build_probe_source(["a.b", "c.d"])
        self.assertEqual(src.splitlines()[0], "import Economy")
        self.assertEqual(src.splitlines()[1:],
                         ["#print axioms a.b", "#print axioms c.d"])


LAKE_SHIM = '''#!/usr/bin/env python3
"""Stand in for `lake -d ROOT env lean PROBE`: answer probes from canned text."""
import sys

DROP = %(drop)r
EXTRA = %(extra)r

probe = sys.argv[-1]
for line in open(probe, encoding="utf-8"):
    line = line.strip()
    if not line.startswith("#print axioms "):
        continue
    name = line.split(" ", 2)[2]
    if name in DROP:
        print("AxiomProbe.lean:1:0: error: unknown identifier '%%s'" %% name)
        continue
    # Lean 4.35 prints the declaration name in single quotes.
    if EXTRA:
        print("'%%s' depends on axioms: [propext, Classical.choice, Quot.sound, %%s]" %% (name, EXTRA))
    else:
        print("'%%s' depends on axioms: [propext, Classical.choice, Quot.sound]" %% name)
'''


def make_lake_shim(dirpath, extra_axiom=None, drop=None):
    """A fake `lake` that answers probes from the file it is handed.

    Args are `lake -d ROOT env lean -D opt... PROBE`; the probe path is the
    last one, which is what the shim echoes against.
    """
    script = os.path.join(dirpath, "lake")
    write(script, LAKE_SHIM % {"drop": list(drop or []), "extra": extra_axiom or ""})
    os.chmod(script, 0o755)
    return script


class KernelAudit(Fixture):

    def names(self):
        return [d.full for d in self.census()["public_kernel"]]

    def test_shim_answers_every_declaration(self):
        tmp = tempfile.mkdtemp(prefix="shim-")
        try:
            lake = make_lake_shim(tmp)
            found, unknown, errors, notes = A.run_kernel_audit(
                self.root, self.names(), lake=lake, batch=1)
            self.assertEqual(sorted(found), sorted(self.names()))
            self.assertEqual((unknown, errors, notes), ([], [], []))
        finally:
            import shutil
            shutil.rmtree(tmp, ignore_errors=True)

    def test_batching_splits_probes(self):
        tmp = tempfile.mkdtemp(prefix="shim-")
        try:
            lake = make_lake_shim(tmp)
            names = ["n%d_result" % i for i in range(5)]
            found, _u, _e, _n = A.run_kernel_audit(
                self.root, names, lake=lake, batch=2, tmpdir=tmp)
            self.assertEqual(len(found), 5)
            probes = sorted(f for f in os.listdir(tmp) if f.startswith("AxiomProbe"))
            self.assertEqual(probes, ["AxiomProbe1.lean", "AxiomProbe2.lean",
                                      "AxiomProbe3.lean"])
            with open(os.path.join(tmp, probes[0]), encoding="utf-8") as fh:
                self.assertEqual(fh.read().splitlines(),
                                 ["import Economy", "#print axioms n0_result",
                                  "#print axioms n1_result"])
        finally:
            import shutil
            shutil.rmtree(tmp, ignore_errors=True)

    def test_missing_toolchain_is_not_success(self):
        with self.assertRaises(RuntimeError):
            A.run_kernel_audit(self.root, self.names(), lake="/nonexistent/lake")

    def test_extra_axiom_is_a_violation(self):
        tmp = tempfile.mkdtemp(prefix="shim-")
        try:
            lake = make_lake_shim(tmp, extra_axiom="mySecretAxiom")
            c = self.census()
            found, unknown, errors, notes = A.run_kernel_audit(
                self.root, [d.full for d in c["public_kernel"]], lake=lake, batch=10)
            v = A.kernel_violations(c, found, unknown, errors, notes)
            self.assertTrue(any("mySecretAxiom" in item for item in v), v)
        finally:
            import shutil
            shutil.rmtree(tmp, ignore_errors=True)

    def test_unknown_declaration_is_a_violation(self):
        tmp = tempfile.mkdtemp(prefix="shim-")
        try:
            lake = make_lake_shim(tmp, drop=["Economy.second_result"])
            c = self.census()
            found, unknown, errors, notes = A.run_kernel_audit(
                self.root, [d.full for d in c["public_kernel"]], lake=lake, batch=10)
            v = A.kernel_violations(c, found, unknown, errors, notes)
            self.assertTrue(any("not a live declaration" in item for item in v), v)
            self.assertTrue(any("no `#print axioms` answer" in item for item in v), v)
        finally:
            import shutil
            shutil.rmtree(tmp, ignore_errors=True)

    def test_clean_profile_has_no_violations(self):
        tmp = tempfile.mkdtemp(prefix="shim-")
        try:
            lake = make_lake_shim(tmp)
            c = self.census()
            found, unknown, errors, notes = A.run_kernel_audit(
                self.root, [d.full for d in c["public_kernel"]], lake=lake, batch=10)
            self.assertEqual(A.kernel_violations(c, found, unknown, errors, notes), [])
        finally:
            import shutil
            shutil.rmtree(tmp, ignore_errors=True)

    def test_silent_batch_is_noticed(self):
        tmp = tempfile.mkdtemp(prefix="shim-")
        try:
            quiet = os.path.join(tmp, "lake")
            write(quiet, "#!/bin/sh\nexit 0\n")
            os.chmod(quiet, 0o755)
            c = self.census()
            found, unknown, errors, notes = A.run_kernel_audit(
                self.root, [d.full for d in c["public_kernel"]], lake=quiet, batch=10)
            self.assertEqual(found, {})
            self.assertTrue(notes)
            self.assertTrue(A.kernel_violations(c, found, unknown, errors, notes))
        finally:
            import shutil
            shutil.rmtree(tmp, ignore_errors=True)


# --------------------------------------------------------------------------
# CLI
# --------------------------------------------------------------------------


class CommandLine(Fixture):

    def test_check_is_clean_on_a_pinned_fixture(self):
        rc, c, report = A.evaluate(self.root)
        self.assertEqual((rc, report["violations"]), (0, []), report["violations"])
        self.assertFalse(report["kernel"])

    def test_json_report_shape(self):
        out = os.path.join(self.root, "report.json")
        rc = A.main(["--root", self.root, "--check", "--quiet", "--json", out])
        self.assertEqual(rc, 0)
        with open(out, encoding="utf-8") as fh:
            payload = json.load(fh)
        self.assertTrue(payload["clean"])
        self.assertEqual(payload["counts"]["lean_files"], 2)
        self.assertEqual(payload["allowed_axioms"], list(A.ALLOWED_AXIOMS))
        self.assertFalse(payload["kernel_verified"])

    def test_kernel_flag_flips_the_report(self):
        tmp = tempfile.mkdtemp(prefix="shim-")
        try:
            lake = make_lake_shim(tmp)
            out = os.path.join(self.root, "kreport.json")
            rc = A.main(["--root", self.root, "--check", "--verify-kernel", "--lake", lake,
                         "--quiet", "--json", out])
            self.assertEqual(rc, 0)
            with open(out, encoding="utf-8") as fh:
                payload = json.load(fh)
            self.assertTrue(payload["kernel_verified"])
            self.assertEqual(payload["kernel_declarations_checked"], 2)
            self.assertEqual(payload["public_kernel_decls"], 2)
        finally:
            import shutil
            shutil.rmtree(tmp, ignore_errors=True)

    def test_missing_lake_exits_2_not_0(self):
        rc = A.main(["--root", self.root, "--check", "--verify-kernel",
                     "--lake", "/nonexistent/lake", "--quiet"])
        self.assertEqual(rc, 2)

    def test_print_census_output_is_reparseable(self):
        text = A.print_census_block(self.root)
        block = A.parse_census_block(text)
        self.assertEqual(set(block), set(A.CENSUS_KEYS))
        self.assertEqual(block["lean_files"], "2")

    def test_default_root_is_the_repository(self):
        self.assertTrue(os.path.isfile(os.path.join(REPO_ROOT, "Economy.lean")))


# --------------------------------------------------------------------------
# Census refresh
# --------------------------------------------------------------------------


class CensusRefresh(Fixture):

    def readme_path(self):
        return os.path.join(self.root, "README.md")

    def test_write_census_repairs_a_stale_block(self):
        path = self.readme_path()
        write(path, self.readme.replace("theorem_count: 2", "theorem_count: 999"))
        stale = A.readme_violations(self.root, A.census(self.root))
        self.assertTrue(any("theorem_count" in item and "999" in item for item in stale), stale)
        A.write_census_block(self.root)
        self.assertEqual(A.readme_violations(self.root, A.census(self.root)), [])

    def test_write_census_is_idempotent(self):
        path = self.readme_path()
        first = A.write_census_block(self.root)
        with open(path, encoding="utf-8") as fh:
            after_first = fh.read()
        second = A.write_census_block(self.root)
        with open(path, encoding="utf-8") as fh:
            after_second = fh.read()
        self.assertEqual(first, second)
        self.assertEqual(after_first, after_second)

    def test_write_census_refuses_a_readme_without_markers(self):
        write(self.readme_path(), "# economy\n\nNothing pinned here.\n")
        with self.assertRaises(SystemExit):
            A.write_census_block(self.root)

    def test_write_census_keeps_the_prose_around_the_block(self):
        A.write_census_block(self.root)
        with open(self.readme_path(), encoding="utf-8") as fh:
            text = fh.read()
        self.assertIn("headline_result", text)
        self.assertIn("```text\n# %s" % A.CENSUS_BEGIN, text)
        self.assertTrue(text.rstrip().endswith("```"))


# --------------------------------------------------------------------------
# Citation extraction
# --------------------------------------------------------------------------


class CitationExtraction(unittest.TestCase):

    def test_plumbing_words_and_paths_are_not_citations(self):
        text = ("uses `sorry`, `native_decide`, `axiom`, `Mathlib.Tactic`, "
                "`propext`, `Classical.choice`, `Quot.sound`, `Economy/Basic.lean`, "
                "`audit_axioms.py`, `--verify-kernel`, `make census`, `lean_files`\n")
        self.assertEqual(A.readme_citations(text), [])

    def test_theorem_shaped_names_are_citations(self):
        text = "| claim | `Economy.Sub.headline_result` | file |\nalso `second_result`\n"
        self.assertEqual(A.readme_citations(text),
                         ["Economy.Sub.headline_result", "second_result"])

    def test_probe_command_name_is_a_citation(self):
        text = "printf ... #print axioms Economy.pipeline_metr_horizon_36mo ...'\n"
        self.assertEqual(A.readme_citations(text), ["Economy.pipeline_metr_horizon_36mo"])


# --------------------------------------------------------------------------
# The real corpus
# --------------------------------------------------------------------------


class RealCorpus(unittest.TestCase):

    def test_head_is_clean_and_pinned(self):
        rc, c, report = A.evaluate(REPO_ROOT)
        self.assertEqual(report["violations"], [], report["violations"])
        self.assertEqual(rc, 0)
        self.assertEqual(c["counts"]["sorry_in_code"], 0)
        self.assertEqual(c["counts"]["native_decide_in_code"], 0)
        self.assertEqual(c["counts"]["user_axioms"], 0)
        self.assertGreaterEqual(c["counts"]["public_kernel_decls"], 200)

    def test_readme_cites_the_headline_theorems(self):
        c = A.census(REPO_ROOT)
        path = os.path.join(REPO_ROOT, "README.md")
        with open(path, encoding="utf-8") as fh:
            cites = A.readme_citations(fh.read())
        universe = A.citation_universe(c)
        fulls = sorted({d.full for d in c["decls"] if d.full})
        for nm in ("pipeline_metr_horizon_36mo",
                   "SolowGrowth.ghost_gdp_constant_labor",
                   "metr_fast_dominates_baseline"):
            self.assertIn(nm, cites)
            self.assertTrue(A.citation_resolves(nm, universe, fulls), nm)

    def test_ci_yaml_wires_the_gate(self):
        self.assertEqual(A.ci_violations(REPO_ROOT), [])

    def test_subprocess_exit_codes(self):
        ok = subprocess.run([sys.executable, os.path.join(SCRIPT_DIR, "audit_axioms.py"),
                             "--root", REPO_ROOT, "--check", "--quiet"],
                            capture_output=True, text=True)
        self.assertEqual(ok.returncode, 0, ok.stdout + ok.stderr)


# --------------------------------------------------------------------------
# Host fairness: the build-slot lease around `lake env lean`
# --------------------------------------------------------------------------
#
# `lake` consults the estate slot table for `lake build` only; `lake env lean`
# walks straight past it and fans out per-core `lean` children that no gated
# caller can preempt. So the kernel pass asks for a slot per probe batch and
# releases it between batches. These tests patch `audit_axioms.subprocess`,
# which keeps them off the host's real slot table and off `timeout(1)`, so the
# argv is asserted exactly instead of skipped on a machine without coreutils.


class FakeSubprocess(object):
    """Answers the two things the audit runs: the slot adapter and `lake`."""

    HELD = "RESULT slot=1 outcome=acquired max=2 waited=0"
    DISABLED = "RESULT slot=-1 outcome=disabled max=0 waited=0"
    # `audit_axioms` names these two through the module it is handed.
    TimeoutExpired = subprocess.TimeoutExpired
    CompletedProcess = subprocess.CompletedProcess

    def __init__(self, acquire_rc=0, acquire_out=None, probe_rc=0):
        self.acquire_rc = acquire_rc
        self.acquire_out = acquire_out
        self.probe_rc = probe_rc
        self.verbs = []          # "acquire" / "release", in order
        self.acquire_argv = None
        self.release_argv = None
        self.probes = []         # argv of every batch, in order

    # -- installed in place of the subprocess module -----------------------

    def run(self, argv, **kwargs):
        return self(argv, **kwargs)

    def __call__(self, argv, **_kwargs):
        argv = [str(a) for a in argv]
        if len(argv) > 2 and argv[1].endswith("slot.py"):
            return self._slot(argv)
        return self._lake(argv)

    def _slot(self, argv):
        verb = argv[2]
        self.verbs.append(verb)
        if verb == "acquire":
            self.acquire_argv = argv
            out = self.acquire_out if self.acquire_out is not None else self.HELD
            return subprocess.CompletedProcess(argv, self.acquire_rc, out + "\n", "")
        self.release_argv = argv
        return subprocess.CompletedProcess(argv, 0, "", "")

    def _lake(self, argv):
        self.probes.append(argv)
        probe = argv[-1]
        lines = []
        try:
            with open(probe, encoding="utf-8") as fh:
                body = fh.read().splitlines()
        except OSError:
            body = []
        for line in body:
            if line.startswith("#print axioms "):
                lines.append("'%s' depends on axioms: "
                             "[propext, Classical.choice, Quot.sound]"
                             % line.split(" ", 2)[2])
        return subprocess.CompletedProcess(argv, self.probe_rc, "\n".join(lines), "")


class SubprocessPatched(unittest.TestCase):
    """Base class: tmpdir fixtures plus the fake subprocess, no real spawns."""

    def setUp(self):
        import shutil
        self.tmp = tempfile.mkdtemp(prefix="lease-")
        self.addCleanup(shutil.rmtree, self.tmp, True)
        # `write` makes the parent directory; these only have to exist, since
        # nothing is executed any more.
        self.adapter = write(os.path.join(self.tmp, "slot.py"), "#!/bin/sh\n")
        self.lake = write(os.path.join(self.tmp, "lake"), "#!/bin/sh\n")
        self.probe_dir = os.path.join(self.tmp, "probes")
        os.makedirs(self.probe_dir)
        self.real_subprocess = A.subprocess
        self.addCleanup(setattr, A, "subprocess", self.real_subprocess)

    def install(self, **kw):
        self.fake = FakeSubprocess(**kw)
        A.subprocess = self.fake
        return self.fake

    def lease(self, **kw):
        kw.setdefault("script", self.adapter)
        kw.setdefault("locks_dir", self.tmp)
        kw.setdefault("log", lambda msg: None)
        return A.BuildSlot(self.tmp, **kw)

    def audit(self, names=("Economy.a",), **kw):
        kw.setdefault("lake", self.lake)
        kw.setdefault("tmpdir", self.probe_dir)
        kw.setdefault("slot_script", self.adapter)
        return A.run_kernel_audit(self.tmp, list(names), **kw)


class BuildSlotLease(SubprocessPatched):

    def test_acquire_then_release_argv(self):
        fake = self.install()
        lease = self.lease()
        lease.acquire()
        self.assertTrue(lease.held)
        self.assertIn("slot=1", lease.note)
        lease.release()
        self.assertFalse(lease.held)
        self.assertEqual(fake.verbs, ["acquire", "release"])
        argv = fake.acquire_argv
        self.assertEqual(argv[1], self.adapter)
        self.assertEqual(argv[2], "acquire")
        self.assertEqual(argv[argv.index("--project") + 1], self.tmp)
        self.assertEqual(argv[argv.index("--pid") + 1], str(os.getpid()))
        self.assertEqual(argv[argv.index("--wait") + 1], str(A.SLOT_WAIT))
        self.assertEqual(argv[argv.index("--dir") + 1], self.tmp)
        self.assertEqual(fake.release_argv[2], "release")

    def test_custom_wait_and_pid_are_forwarded(self):
        fake = self.install()
        self.lease(wait=5, pid=4242).acquire()
        argv = fake.acquire_argv
        self.assertEqual(argv[argv.index("--wait") + 1], "5")
        self.assertEqual(argv[argv.index("--pid") + 1], "4242")

    def test_context_manager_releases_on_exception(self):
        fake = self.install()
        with self.assertRaises(ValueError):
            with self.lease() as lease:
                self.assertTrue(lease.held)
                raise ValueError("probe died mid-batch")
        self.assertEqual(fake.verbs, ["acquire", "release"])

    def test_refusal_raises_instead_of_running_unleased(self):
        fake = self.install(acquire_rc=75)
        with self.assertRaises(A.SlotRefused):
            self.lease().acquire()
        self.assertEqual(fake.verbs, ["acquire"])

    def test_broken_adapter_raises_not_passes(self):
        fake = self.install(acquire_rc=1)
        with self.assertRaises(A.SlotRefused):
            self.lease().acquire()

    def test_disabled_table_is_admitted_but_not_held(self):
        fake = self.install(acquire_out=FakeSubprocess.DISABLED)
        lease = self.lease()
        lease.acquire()
        self.assertFalse(lease.held)
        lease.release()
        self.assertEqual(fake.verbs, ["acquire"])
        self.assertIn("slot=-1", lease.note)

    def test_parent_lease_is_passed_through(self):
        fake = self.install()
        os.environ[A.SLOT_HELD_ENV] = "1"
        self.addCleanup(os.environ.pop, A.SLOT_HELD_ENV, None)
        lease = self.lease()
        lease.acquire()
        self.assertFalse(lease.held)
        self.assertIn("parent", lease.note)
        lease.release()
        self.assertEqual(fake.verbs, [])

    def test_absent_adapter_is_announced_not_silenced(self):
        fake = self.install()
        lease = self.lease(script=os.path.join(self.tmp, "no-slot.py"))
        lease.acquire()
        self.assertFalse(lease.held)
        self.assertIn("wall clock", lease.note)
        self.assertEqual(fake.verbs, [])

    def test_switch_off_is_announced(self):
        fake = self.install()
        lease = self.lease(enabled=False)
        lease.acquire()
        self.assertFalse(lease.held)
        self.assertIn("--no-slot", lease.note)
        self.assertEqual(fake.verbs, [])

    def test_kill_switch_closes_the_default_adapter_only(self):
        # ECONOMY_AUDIT_NO_SLOT is set for the whole suite, so a plain
        # BuildSlot must never queue behind the host's real slot table...
        self.assertFalse(self.lease(script=None).enabled)
        # ...while a caller that names its adapter explicitly still leases.
        self.assertTrue(self.lease().enabled)


class ProbeBatchCommand(SubprocessPatched):

    def split_guard(self, argv):
        """(wall seconds, the lake argv), or (None, argv) if unguarded."""
        guard = A._timeout_wrapper()
        if guard and argv[:1] == guard:
            return argv[1], argv[2:]
        return None, argv

    def test_command_is_the_lakefile_lean_options(self):
        fake = self.install(acquire_out=FakeSubprocess.DISABLED)
        self.audit(["Economy.a", "Economy.b"])
        self.assertEqual(len(fake.probes), 1)
        _secs, lake_argv = self.split_guard(fake.probes[0])
        self.assertEqual(lake_argv[0], self.lake)
        self.assertEqual(lake_argv[1:3], ["-d", self.tmp])
        self.assertEqual(lake_argv[3:5], ["env", "lean"])
        self.assertIn("autoImplicit=false", lake_argv)
        self.assertTrue(lake_argv[-1].endswith(".lean"))

    def test_wall_guard_is_always_in_front(self):
        fake = self.install(acquire_out=FakeSubprocess.DISABLED)
        self.audit()
        if not A._timeout_wrapper():
            self.skipTest("no timeout(1) on this host")
        self.assertEqual(fake.probes[0][0], A._timeout_wrapper()[0])

    def test_unleased_batch_gets_the_estate_bound(self):
        fake = self.install()
        self.audit(use_slot=False)
        self.assertEqual(A.PROBE_UNLEASED_S, 120)
        secs, _argv = self.split_guard(fake.probes[0])
        if secs is None:
            self.skipTest("no timeout(1) on this host")
        self.assertEqual(secs, str(A.PROBE_UNLEASED_S))
        self.assertEqual(fake.verbs, [])

    def test_leased_batch_gets_the_longer_bound(self):
        fake = self.install()
        self.audit()
        secs, _argv = self.split_guard(fake.probes[0])
        if secs is None:
            self.skipTest("no timeout(1) on this host")
        self.assertEqual(secs, str(A.PROBE_LEASED_S))

    def test_explicit_timeout_beats_both_defaults(self):
        fake = self.install()
        self.audit(timeout=7)
        secs, _argv = self.split_guard(fake.probes[0])
        if secs is None:
            self.skipTest("no timeout(1) on this host")
        self.assertEqual(secs, "7")

    def test_one_lease_per_batch_not_one_per_audit(self):
        fake = self.install()
        found, _u, _e, _n = self.audit(
            ["Economy.a", "Economy.b", "Economy.c"], batch=2)
        self.assertEqual(len(fake.probes), 2)
        self.assertEqual(fake.verbs,
                         ["acquire", "release", "acquire", "release"])
        self.assertEqual(sorted(found), ["Economy.a", "Economy.b", "Economy.c"])

    def test_refused_lease_never_reaches_the_compiler(self):
        fake = self.install(acquire_rc=75)
        with self.assertRaises(A.SlotRefused):
            self.audit(["Economy.a", "Economy.b"], batch=1)
        self.assertEqual(fake.probes, [])

    def test_a_walled_batch_is_an_error_not_a_pass(self):
        fake = self.install(probe_rc=124)
        _f, _u, errors, _n = self.audit()
        self.assertTrue(any("wall bound" in e for e in errors), errors)

    def test_answers_are_read_from_the_kernel(self):
        self.install()
        found, unknown, errors, notes = self.audit(["Economy.a"])
        self.assertEqual(found, {"Economy.a": ["propext", "Classical.choice",
                                               "Quot.sound"]})
        self.assertEqual((unknown, errors, notes), ([], [], []))


if __name__ == "__main__":
    unittest.main(verbosity=2)
