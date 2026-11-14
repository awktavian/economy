#!/usr/bin/env python3
"""Bind a checkout's Lake packages to the estate's warm Mathlib generation.

Why this exists. A CI job that seeds Mathlib with `lake exe cache get` has to
download and unpack the library every run. Measured on run 43547320929 of this
repository: that step ran 02:43:11 -> 03:27:31, 44m20s, and was cut by the job's
45-minute ceiling, which cancelled the job and skipped every step after it —
including the axiom gate itself. The corpus was never checked, and the run
concluded `cancelled` for the fourth time in a row.

The estate does not have that problem, because it already keeps one built
Mathlib per revision in a machine-wide cache (`~/.lean-cache/mathlib/<rev>/`)
and every lane reaches it by symlinking the whole package directory, per
`~/.claude/contracts/mathlib-warm-cache.json` (`lean_path_layout`: "repos
symlink the whole PACKAGE DIR ... and let Lake derive LEAN_PATH"). Measured
2026-11-14 in a clean-room CI-style checkout (a `git archive` of HEAD, no
`.lake`, 18-core host): with those symlinks in place, `lake build Economy`
completed 3284 jobs in 123.64s, rc 0, with no download at all.

So this script does the linking and nothing else, under three rules:

  * It only ever CREATES a link where the destination is absent or an empty
    directory. It never deletes, never empties, and never writes through a
    symlink it did not just make — a `rm -rf` or a tar extract aimed at a
    package dir lands in the shared generation and corrupts every other build
    on the host (that vector is `leanprover/lean-action`'s `use-github-cache`,
    measured on awkronos/jill).
  * A package already symlinked somewhere else is reported as DRIFT and is not
    touched. Building against a generation the manifest does not name would
    produce a verdict about the wrong library, and the fallback fetch is
    refused too, because it would write through that link.
  * A generation that is absent or unverified is reported, not silently built.
    The contract's fail-closed rule is that a stale or missing warm cache is a
    finding; a from-source Mathlib build is hours, and it is what turns a job
    into a cancellation.

Exit codes: 0 the corpus can be built (every package resolved, after --apply),
1 a package is missing or drifted (caller must not build), 2 this instrument
could not run at all (no manifest, unreadable cache).

Usage:
    python3 scripts/warm_cache.py --plan            # read-only report
    python3 scripts/warm_cache.py --apply           # create the links
    python3 scripts/warm_cache.py --apply --json /tmp/warm.json
"""

from __future__ import annotations

import argparse
import json
import os
import sys

#: Manifest name -> the name the cache generation may use on a case-insensitive
#: volume. Resolved by lookup, never assumed; see `match_package`.
CACHE_SUBDIR = os.path.join("mathlib")
#: A package dir counts as warm only if this lives under it and is non-empty:
#: it is the entry suffix the contract names for a raw-`lean` consumer.
OLEAN_SUFFIX = os.path.join(".lake", "build", "lib", "lean")

#: Root search order, from the contract's `cache_root_accessor`: an explicit
#: override, then the CI root, then the dev root. `~/.lean-cache-ci` is itself a
#: link to the shared store on this host, which is why both are listed.
ROOT_ENV = "KAGAMI_LEAN_CACHE_ROOT"
ROOT_CANDIDATES = (
    os.path.expanduser("~/.lean-cache-ci"),
    os.path.expanduser("~/.lean-cache"),
)


class WarmRefused(RuntimeError):
    """The warm generation cannot serve this checkout. Never repaired by force."""


def repo_root(default=None):
    here = default or os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    return os.path.abspath(here)


def manifest_packages(root):
    """[(name, full_rev)] from lake-manifest.json, manifest order."""
    path = os.path.join(root, "lake-manifest.json")
    if not os.path.isfile(path):
        raise WarmRefused("lake-manifest.json is missing from %s" % root)
    try:
        with open(path, "r", encoding="utf-8") as fh:
            data = json.load(fh)
    except (OSError, ValueError) as exc:
        raise WarmRefused("lake-manifest.json unreadable: %s" % exc)
    out = []
    for pkg in data.get("packages") or []:
        name = pkg.get("name")
        rev = (pkg.get("rev") or "").strip()
        if name:
            out.append((name, rev))
    if not out:
        raise WarmRefused("lake-manifest.json lists no packages")
    return out


def mathlib_rev(packages):
    for name, rev in packages:
        if name.lower() == "mathlib":
            return rev
    raise WarmRefused("the manifest has no mathlib entry, so there is no"
                      " generation to bind to")


def cache_roots():
    """The roots to ask, in contract order.

    An explicit `KAGAMI_LEAN_CACHE_ROOT` is asked ALONE. The contract makes that
    variable the whole repoint ("nothing needs a new contract"), so a consumer
    that quietly fell back to `~/.lean-cache` after the operator moved the cache
    would build against a generation the operator believed retired. Absent
    instead of silently redirected is the useful answer.
    """
    override = os.environ.get(ROOT_ENV)
    if override:
        return [os.path.abspath(os.path.expanduser(override))]
    seen, out = set(), []
    for r in ROOT_CANDIDATES:
        if r not in seen:
            seen.add(r)
            out.append(r)
    return out


def find_generation(packages, log=None):
    """(generation_dir, root) for the manifest's mathlib revision, or raise.

    Every root is asked, in contract order. A generation directory that exists
    but has not been verified as built is still returned — the per-package check
    below is what proves it is warm, so a half-populated cache reads as the
    specific packages it lacks rather than as a missing root.
    """
    rev = mathlib_rev(packages)
    roots = cache_roots()
    for root in roots:
        gen = os.path.join(root, CACHE_SUBDIR, rev)
        if os.path.isdir(gen):
            return gen, root
    raise WarmRefused("no warm generation for mathlib %s under %s%s"
                      % (rev, ", ".join(roots),
                         " (KAGAMI_LEAN_CACHE_ROOT names only that root; it is"
                         " not consulted elsewhere on purpose)"
                         if os.environ.get(ROOT_ENV) else ""))


def match_package(gen, name):
    """The generation's own spelling of `name`, or None.

    macOS volumes are case-insensitive but lake treats module paths as case
    exact, and the estate has measured what that costs: a second spelling of a
    shared package makes lake remove what it thinks is a stale artifact, and on
    a case-folded name that removes a live olean from the shared generation
    (lane CACHE-L2SPACE-CURE-1103). So the link uses the manifest's name, which
    is what lake will look for, while the target is read back from the
    generation's own directory entry, which is what already exists.
    """
    try:
        entries = os.listdir(gen)
    except OSError:
        return None
    if name in entries:
        return name
    folded = {e.lower(): e for e in entries}
    return folded.get(name.lower())


def package_warm(gen, spelling):
    real = os.path.join(gen, spelling)
    lean_dir = os.path.join(real, OLEAN_SUFFIX)
    if not os.path.isdir(lean_dir):
        return False, "%s has no %s" % (spelling, OLEAN_SUFFIX)
    try:
        if not os.listdir(lean_dir):
            return False, "%s is empty" % OLEAN_SUFFIX
    except OSError as exc:
        return False, "%s unreadable: %s" % (OLEAN_SUFFIX, exc)
    return True, ""


def same_dir(a, b):
    """True when two paths are the same directory, not just the same string.

    Needed because this estate's volumes are case-insensitive: a link written as
    `.../plausible` and a generation entry named `Plausible` are one directory,
    and comparing spellings would read that as drift. `os.path.samefile` answers
    with inodes, so the case of the spelling stops mattering.
    """
    try:
        return os.path.samefile(a, b)
    except OSError:
        return os.path.realpath(a) == os.path.realpath(b)


def state_of(link, gen, spelling):
    """Classify one destination path without touching it."""
    target = os.path.join(gen, spelling)
    if os.path.islink(link):
        try:
            raw = os.readlink(link)
        except OSError:
            raw = ""
        got = raw if os.path.isabs(raw) else os.path.join(os.path.dirname(link), raw)
        if got and same_dir(got, target):
            return "linked", "already bound to the generation"
        return "drift", "symlinked to %s, manifest wants %s" % (got or "?", target)
    if os.path.isdir(link):
        try:
            empty = not os.listdir(link)
        except OSError:
            empty = False
        if empty:
            return "empty", "empty directory, a link can replace it"
        return "real", "a real directory this job does not own"
    if os.path.exists(link):
        return "file", "not a directory"
    return "missing", "absent"


def plan(root, log=None):
    """[(name, state, note, target_or_"")] for every manifest package."""
    log = log or (lambda m: None)
    packages = manifest_packages(root)
    gen, base = find_generation(packages)
    log("  warm generation %s (root %s, mathlib %s)"
        % (gen, base, mathlib_rev(packages)))
    rows = []
    pkgs_dir = os.path.join(root, ".lake", "packages")
    for name, _rev in packages:
        spelling = match_package(gen, name)
        if spelling is None:
            rows.append((name, "absent", "the generation has no such package", ""))
            continue
        ok, why = package_warm(gen, spelling)
        if not ok:
            rows.append((name, "cold", "%s is not built: %s" % (spelling, why), ""))
            continue
        link = os.path.join(pkgs_dir, name)
        state, note = state_of(link, gen, spelling) if os.path.isdir(pkgs_dir) \
            else ("missing", "absent")
        rows.append((name, state, note, os.path.join(gen, spelling)))
    return gen, rows


def apply_links(root, log=None):
    """Create the links this plan calls for. Returns (gen, rows_after)."""
    log = log or (lambda m: None)
    gen, rows = plan(root, log)
    pkgs_dir = os.path.join(root, ".lake", "packages")
    out = []
    for name, state, note, target in rows:
        if state in ("linked",):
            out.append((name, state, note, target))
            continue
        if not target:
            out.append((name, state, note, ""))
            continue
        if state not in ("missing", "empty"):
            out.append((name, state, "refused: %s" % note, target))
            continue
        link = os.path.join(pkgs_dir, name)
        if state == "empty":
            try:
                os.rmdir(link)          # only ever an EMPTY directory
            except OSError as exc:
                out.append((name, "error", "empty dir not removable: %s" % exc,
                            target))
                continue
        try:
            os.makedirs(pkgs_dir, exist_ok=True)
            os.symlink(target, link)
        except OSError as exc:
            out.append((name, "error", str(exc), target))
            continue
        log("  linked .lake/packages/%s -> %s" % (name, target))
        out.append((name, "linked", "created", target))
    return gen, out


def blocking(rows):
    """Packages that make a build against this generation unsound to run."""
    bad = []
    for name, state, note, _t in rows:
        if state in ("drift", "real", "file", "error", "absent", "cold"):
            bad.append("%s (%s: %s)" % (name, state, note))
    return bad


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--root", default=None, help="checkout to bind (default:"
                                                " parent of scripts/)")
    mode = ap.add_mutually_exclusive_group()
    mode.add_argument("--plan", action="store_true", help="read-only report"
                                                          " (default)")
    mode.add_argument("--apply", action="store_true", help="create the links")
    ap.add_argument("--json", dest="json_out", help="write the report here")
    ap.add_argument("--quiet", action="store_true")
    args = ap.parse_args(argv)

    root = repo_root(args.root)
    log = (lambda m: None) if args.quiet else print
    try:
        gen, rows = (apply_links(root, log) if args.apply else plan(root, log))
    except WarmRefused as exc:
        print("WARM-CACHE REFUSED: %s" % exc)
        print("  This host has no usable warm generation, so the corpus must not"
              " be built from source here either. A bounded `lake exe cache get`"
              " is the fallback for a runner with no estate cache; on the estate"
              " the answer is to warm the generation, not to download a second"
              " copy of it.")
        return 1

    bad = blocking(rows)
    if args.json_out:
        payload = {
            "root": root,
            "generation": gen,
            "applied": bool(args.apply),
            "packages": [{"name": n, "state": s, "note": d, "target": t}
                         for n, s, d, t in rows],
            "blocking": bad,
            "ready": not bad,
        }
        with open(args.json_out, "w", encoding="utf-8") as fh:
            json.dump(payload, fh, indent=2, sort_keys=True)
            fh.write("\n")

    counts = {}
    for _n, s, _d, _t in rows:
        counts[s] = counts.get(s, 0) + 1
    print("warm cache bind — %s" % root)
    print("  generation: %s" % gen)
    print("  packages: %s" % ", ".join("%s=%d" % kv for kv in sorted(counts.items())))
    for n, s, d, _t in rows:
        if s in ("linked",):
            continue
        print("  %s: %s — %s" % (n, s, d))
    if bad:
        print("NOT READY (%d package(s)) — refusing to build against this"
              " generation: %s" % (len(bad), "; ".join(bad[:3])))
        return 1
    print("READY: %d package(s) resolve to the warm generation%s"
          % (len(rows), "" if args.apply else " (plan only, nothing written)"))
    return 0


if __name__ == "__main__":
    sys.exit(main())
