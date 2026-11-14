#!/usr/bin/env python3
"""Tests for scripts/warm_cache.py — the CI cache-bind instrument.

Hermetic: every case builds a temporary fake generation and points
KAGAMI_LEAN_CACHE_ROOT at it, so nothing reads or writes the machine-wide cache
and nothing needs a Lean toolchain. What is under test is the safety of the
bind, not lake's behaviour: the instrument must only ever CREATE a link where
nothing real stands, must refuse to touch a package bound elsewhere, and must
report a cold or absent generation instead of letting a from-source build start.
"""

import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, SCRIPT_DIR)

import warm_cache as W  # noqa: E402

REV = "0123456789abcdef0123456789abcdef0123456789"
PACKAGES = ["mathlib", "batteries", "Cli"]


def write(path, text):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w", encoding="utf-8") as fh:
        fh.write(text)
    return path


class Fixture(unittest.TestCase):
    """A checkout plus a fake warm generation, with the root forced by env."""

    def setUp(self):
        self.tmp = tempfile.mkdtemp(prefix="warmcache-")
        self.addCleanup(shutil.rmtree, self.tmp, True)
        self.root = os.path.join(self.tmp, "checkout")
        self.cache = os.path.join(self.tmp, "cache")
        self.gen = os.path.join(self.cache, "mathlib", REV)
        os.makedirs(self.root)
        os.makedirs(self.gen)
        manifest = {"version": "1.2.0",
                    "packages": [{"name": n, "rev": REV,
                                  "url": "https://example.invalid/%s" % n}
                                 for n in PACKAGES]}
        write(os.path.join(self.root, "lake-manifest.json"),
              json.dumps(manifest) + "\n")
        # the cache layout the contract names: <gen>/<pkg>/.lake/build/lib/lean
        for n in PACKAGES:
            write(os.path.join(self.gen, n, ".lake", "build", "lib", "lean",
                               "%s.olean" % n), "olean")
        self._env = os.environ.get(W.ROOT_ENV)
        os.environ[W.ROOT_ENV] = self.cache
        self.addCleanup(self._restore_env)

    def _restore_env(self):
        if self._env is None:
            os.environ.pop(W.ROOT_ENV, None)
        else:
            os.environ[W.ROOT_ENV] = self._env

    def link(self, name):
        return os.path.join(self.root, ".lake", "packages", name)

    def states(self, rows=None):
        rows = rows if rows is not None else W.plan(self.root)[1]
        return {n: s for n, s, _d, _t in rows}

    def tree(self, path):
        """(relpath, islink_target_or_"") for everything under path."""
        out = []
        for dirpath, dirnames, filenames in os.walk(path):
            dirnames.sort()
            for f in sorted(filenames):
                full = os.path.join(dirpath, f)
                out.append((os.path.relpath(full, path),
                            os.readlink(full) if os.path.islink(full) else ""))
        return sorted(out)


class Plan(Fixture):

    def test_a_fresh_checkout_is_all_missing(self):
        self.assertEqual(self.states(), {n: "missing" for n in PACKAGES})

    def test_apply_links_every_package_and_reports_ready(self):
        _gen, rows = W.apply_links(self.root)
        self.assertEqual(self.states(rows), {n: "linked" for n in PACKAGES})
        for n in PACKAGES:
            self.assertTrue(os.path.islink(self.link(n)), n)
            self.assertTrue(W.same_dir(self.link(n), os.path.join(self.gen, n)))

    def test_apply_is_idempotent(self):
        before = self.tree(self.gen)
        W.apply_links(self.root)
        _gen, rows = W.apply_links(self.root)
        self.assertEqual(self.states(rows), {n: "linked" for n in PACKAGES})
        self.assertEqual(self.tree(self.gen), before)

    def test_the_generation_is_never_written_to(self):
        """The whole point of a bind: read the cache, write nothing into it."""
        before = self.tree(self.gen)
        W.apply_links(self.root)
        self.assertEqual(self.tree(self.gen), before)
        # and the checkout's own build dir is NOT pre-created by the instrument
        self.assertFalse(os.path.exists(os.path.join(self.root, ".lake",
                                                     "build")))

    def test_a_package_the_generation_lacks_blocks_the_build(self):
        shutil.rmtree(os.path.join(self.gen, "Cli"))
        rows = W.plan(self.root)[1]
        self.assertEqual(self.states(rows)["Cli"], "absent")
        self.assertTrue(any(e.startswith("Cli ") for e in W.blocking(rows)))
        _gen, after = W.apply_links(self.root)
        self.assertFalse(os.path.exists(self.link("Cli")),
                         "a missing package must not get a dangling link")

    def test_an_unbuilt_package_is_cold_not_warm(self):
        shutil.rmtree(os.path.join(self.gen, "batteries", ".lake"))
        rows = W.plan(self.root)[1]
        self.assertEqual(self.states(rows)["batteries"], "cold")
        self.assertTrue(W.blocking(rows))
        W.apply_links(self.root)
        self.assertFalse(os.path.islink(self.link("batteries")),
                         "a cold package must not be bound — lake would then"
                         " build Mathlib from source inside the shared tree")

    def test_an_empty_directory_is_replaced_by_a_link(self):
        os.makedirs(self.link("Cli"))
        self.assertEqual(self.states()["Cli"], "empty")
        W.apply_links(self.root)
        self.assertTrue(os.path.islink(self.link("Cli")))

    def test_a_populated_real_directory_is_never_removed(self):
        """The destructive case. A real dir means something else owns it."""
        planted = write(os.path.join(self.link("Cli"), "someone-elses.olean"),
                        "payload")
        self.assertEqual(self.states()["Cli"], "real")
        _gen, rows = W.apply_links(self.root)
        self.assertTrue(os.path.isfile(planted), "the instrument deleted work")
        self.assertFalse(os.path.islink(self.link("Cli")))
        self.assertTrue(any(e.startswith("Cli (real") for e in W.blocking(rows)),
                        "a real dir must read as blocking, so CI refuses to"
                        " build against a tree it does not own")

    def test_a_regular_file_in_place_of_a_package_is_reported(self):
        write(self.link("Cli"), "not a directory")
        self.assertEqual(self.states()["Cli"], "file")
        W.apply_links(self.root)
        self.assertFalse(os.path.islink(self.link("Cli")))

    def test_a_link_elsewhere_is_drift_and_is_left_alone(self):
        other = os.path.join(self.tmp, "other-gen")
        os.makedirs(os.path.join(other, "Cli", ".lake", "build", "lib", "lean"))
        os.makedirs(os.path.dirname(self.link("Cli")), exist_ok=True)
        os.symlink(other, self.link("Cli"))
        rows = W.plan(self.root)[1]
        self.assertEqual(self.states(rows)["Cli"], "drift")
        W.apply_links(self.root)
        self.assertEqual(os.readlink(self.link("Cli")), other,
                         "drift must be reported, not silently repointed")

    def test_a_link_to_the_same_generation_by_another_spelling_is_linked(self):
        """Case-insensitive volumes: `.../plausible` and `Plausible` are one dir.

        Comparing spellings instead of inodes would call this drift and refuse a
        perfectly good bind; comparing inodes is what makes the check true on
        both this host and a case-sensitive CI runner.
        """
        probe = os.path.join(self.tmp, "case-probe")
        os.makedirs(os.path.join(probe, "Mixed"))
        case_insensitive = os.path.isdir(os.path.join(self.tmp,
                                                      "case-probe", "mixed"))
        if not case_insensitive:
            self.skipTest("volume is case-sensitive; nothing to fold")
        os.makedirs(os.path.dirname(self.link("Cli")), exist_ok=True)
        os.symlink(os.path.join(self.gen, "cli"), self.link("Cli"))
        self.assertEqual(self.states()["Cli"], "linked")


class Roots(Fixture):

    def test_an_explicit_root_is_asked_alone(self):
        """KAGAMI_LEAN_CACHE_ROOT is the whole repoint; falling back would
        build against a generation the operator moved away from."""
        os.environ[W.ROOT_ENV] = os.path.join(self.tmp, "moved-away")
        with self.assertRaises(W.WarmRefused) as cm:
            W.find_generation(W.manifest_packages(self.root))
        self.assertIn("moved-away", str(cm.exception))
        self.assertNotIn(self.cache, str(cm.exception))

    def test_the_contract_roots_are_tried_in_order(self):
        self.assertEqual(W.cache_roots(), [self.cache])
        del os.environ[W.ROOT_ENV]
        roots = W.cache_roots()
        self.assertEqual(roots[0], os.path.expanduser("~/.lean-cache-ci"))
        self.assertIn(os.path.expanduser("~/.lean-cache"), roots)

    def test_no_manifest_is_a_refusal(self):
        empty = os.path.join(self.tmp, "empty")
        os.makedirs(empty)
        with self.assertRaises(W.WarmRefused):
            W.manifest_packages(empty)

    def test_a_manifest_without_mathlib_is_a_refusal(self):
        write(os.path.join(self.root, "lake-manifest.json"),
              json.dumps({"packages": [{"name": "batteries", "rev": REV}]}))
        with self.assertRaises(W.WarmRefused):
            W.mathlib_rev(W.manifest_packages(self.root))

    def test_an_absent_generation_is_reported_not_built(self):
        shutil.rmtree(self.gen)
        with self.assertRaises(W.WarmRefused):
            W.find_generation(W.manifest_packages(self.root))


class Cli(Fixture):

    def run_cli(self, *args):
        argv = [sys.executable, os.path.join(SCRIPT_DIR, "warm_cache.py")] + \
            list(args)
        return subprocess.run(argv, capture_output=True, text=True, cwd=SCRIPT_DIR)

    def test_plan_exits_ready_and_writes_nothing(self):
        proc = self.run_cli("--root", self.root, "--plan")
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        self.assertIn("READY", proc.stdout)
        self.assertIn("plan only", proc.stdout)
        self.assertFalse(os.path.exists(os.path.join(self.root, ".lake")))

    def test_apply_then_plan_is_linked(self):
        self.assertEqual(self.run_cli("--root", self.root, "--apply")
                         .returncode, 0)
        self.assertEqual(self.states(), {n: "linked" for n in PACKAGES})

    def test_a_blocking_package_exits_one(self):
        shutil.rmtree(os.path.join(self.gen, "batteries", ".lake"))
        proc = self.run_cli("--root", self.root, "--apply")
        self.assertEqual(proc.returncode, 1, proc.stdout)
        self.assertIn("NOT READY", proc.stdout)
        self.assertIn("batteries", proc.stdout)

    def test_a_missing_generation_exits_one_with_the_reason(self):
        shutil.rmtree(self.gen)
        proc = self.run_cli("--root", self.root, "--apply")
        self.assertEqual(proc.returncode, 1, proc.stdout)
        self.assertIn("WARM-CACHE REFUSED", proc.stdout)
        self.assertIn("bounded", proc.stdout,
                      "the message must name the fallback for a non-estate runner")

    def test_json_records_states_and_readiness(self):
        out = os.path.join(self.tmp, "warm.json")
        proc = self.run_cli("--root", self.root, "--apply", "--json", out)
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        with open(out, encoding="utf-8") as fh:
            d = json.load(fh)
        self.assertTrue(d["ready"])
        self.assertTrue(d["applied"])
        self.assertEqual(d["generation"], self.gen)
        self.assertEqual(sorted(p["name"] for p in d["packages"]),
                         sorted(PACKAGES))
        self.assertEqual({p["state"] for p in d["packages"]}, {"linked"})
        self.assertEqual(d["blocking"], [])


if __name__ == "__main__":
    unittest.main(verbosity=2)
