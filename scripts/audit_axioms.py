#!/usr/bin/env python3
"""Executable axiom / sorry gate for the `economy` Lean 4 corpus.

The repository claims one thing above everything else (CLAUDE.md "The
invariant"): zero `sorry`, zero user-defined axioms, and every exported
theorem kernel-clean under `[propext, Classical.choice, Quot.sound]`.  Until
now that claim was only prose in README.md, so nothing stopped it from going
stale.  This script turns the prose into a gate.

Modes
-----
default / ``--check``
    Static gate, no compiler needed:

    * comment- and string-stripped scans, so the word "sorry" inside a
      docstring cannot be counted as code and a real one cannot hide in prose;
    * a declaration census with full Lean names resolved through the
      ``namespace`` stack;
    * hard bans: ``sorry``, ``native_decide``, ``sorryAx``, user ``axiom``
      declarations, and the TN placeholders CLAUDE.md hard rule 2 forbids
      (``:= True``, ``:= PUnit``, ``:= trivial``, ``:= ⊥``);
    * README parity: the machine census block must equal what the corpus
      actually contains, and every theorem cited in the Receipts table must
      still resolve to a live declaration;
    * forecast-table parity: every ``Economy/<File>.lean:<N>`` citation in
      ``forecasts/forecast_table.md`` must name, in its own context, a
      declaration the census measures at exactly that line — the one
      citation form that moves with every edit above the cited
      declaration, and nothing was watching it (see
      ``forecast_violations``);
    * ``.github/workflows/ci.yml`` invariants, including symlink-safe cache
      seeding (a symlinked ``.lake/packages/<pkg>`` prefix lets an unguarded
      ``lake exe cache get`` write through into the machine-wide cache).

``--verify-kernel``
    Everything above, plus the compiler: generate ``#print axioms`` probe
    harnesses (batched, because a single Lean parse error stops the compiler
    reporting anything after it), run them with ``lake -d <root> env lean``,
    and require that every public theorem/lemma in the census is reported by
    the kernel and that each reported axiom set is a subset of the allowed
    foundational axioms.

Exit status: ``0`` clean, ``1`` violations found, ``2`` the gate could not run
(missing toolchain).  A gate that cannot run never reports success.

Usage
-----
    python3 scripts/audit_axioms.py --check
    python3 scripts/audit_axioms.py --check --verify-kernel
    python3 scripts/audit_axioms.py --check --json /tmp/axiom-audit.json
    python3 scripts/audit_axioms.py --print-census
    python3 scripts/audit_axioms.py --write-census
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile

# --------------------------------------------------------------------------
# Contract constants
# --------------------------------------------------------------------------

#: The only axioms a kernel-clean Lean 4 proof may rest on.
ALLOWED_AXIOMS = ("propext", "Classical.choice", "Quot.sound")

#: Markers of the machine-readable census block in README.md.
CENSUS_BEGIN = "audit-census:begin"
CENSUS_END = "audit-census:end"

#: Census keys README.md must carry, in the order --print-census emits them.
#:   lean_files            how many .lean files the gate scanned
#:   theorem_count         `theorem` declarations (any visibility)
#:   lemma_count           `lemma` declarations
#:   other_decl_count      def/abbrev/structure/class/instance/opaque/axiom
#:   private_decls         declarations `private` (the kernel cannot see them
#:                         from an importing file, so they are not kernel-checked)
#:   public_kernel_decls   theorem+lemma declarations the kernel gate must answer for
#:   sorry_in_code         `sorry` tokens outside comments and strings
#:   native_decide_in_code `native_decide` tokens outside comments
#:   user_axioms           `axiom` declarations in this corpus
#:   placeholders          theorem/lemma bodies of `:= True|PUnit|trivial|⊥`
#:   theorem_citations     corpus names README.md cites and must keep resolving
#:   allowed_axioms        the kernel-clean axiom profile
CENSUS_KEYS = (
    "lean_files",
    "theorem_count",
    "lemma_count",
    "other_decl_count",
    "private_decls",
    "public_kernel_decls",
    "sorry_in_code",
    "native_decide_in_code",
    "user_axioms",
    "placeholders",
    "theorem_citations",
    "allowed_axioms",
)

#: ---------------------------------------------------------------------
#: Host fairness for the kernel pass.
#:
#: `lake env lean` is invisible to `lean-build-slot.py`: it fans out per-core
#: `lean` children that compete with every admitted `lake build` on the host.
#: So the kernel pass takes a slot before each probe batch and releases it on
#: the way out. If no lease is held (clean checkout, --no-slot, an adapter the
#: estate does not run), the batch is bounded by PROBE_UNLEASED_S instead, and
#: a lease failure is reported rather than run around.
#: ---------------------------------------------------------------------
SLOT_SCRIPT = os.path.expanduser("~/.claude/scripts/lean-build-slot.py")
SLOT_HELD_ENV = "KAGAMI_LEAN_BUILD_SLOT_HELD"
LOCKS_DIR_ENV = "KAGAMI_LOCKS_DIR"
DEFAULT_LOCKS_DIR = "/tmp/kagami-locks"
SLOT_WAIT = 180  # seconds to wait for a free build slot
PROBE_UNLEASED_S = 120  # estate bound on an unleased `lake env lean`
# Measured twice on the same 18-core estate host with warm caches. Idle, the
# whole `--verify-kernel` pass is 4 batches over the public declarations in
# 109.44s at head bac6a9e3, and 273.48s under contention, where one batch spent
# 171.5s waiting for a slot and still finished inside its bound. The bound was
# then broken, by this repository's own CI: on 2026-11-14, with the CI kernel
# leg running the same pass on the same host, batch 3 (80 declarations) passed
# 300s without answering -- rc=124, whole pass 842.20s, and lake reported
# `batteries: repository has local changes` on `.lake/packages/batteries`, which
# is a symlink into the machine-wide cache. That gate then printed 81 violations
# reading like an unsound corpus, when the kernel had simply never been asked.
#
# So 300s is a bound a busy host CAN exceed while nothing is wrong with the
# corpus. It stays small because `batches x bound` must fit the CI job's
# 45-minute ceiling, and what changed is what a wall means: a walled batch is
# split and retried, and a wall that survives splitting down to one declaration
# exits EX_TEMPFAIL as unverified, never as a soundness verdict.
PROBE_LEASED_S = 300  # backstop while a slot is held
#: A walled batch is halved and retried until the chunk is this small; at one
#: declaration there is nothing left to split, so it is reported unverified.
WALL_SPLIT_FLOOR = 1
#: Cap on the split depth of one lineage (80 -> 40 -> 20 -> 10 -> 5 -> 2 -> 1),
#: so a wedged compiler cannot make the pass grow without bound.
WALL_SPLIT_DEPTH = 7
#: Prefix on an error that means "the compiler did not answer", as opposed to
#: "the kernel answered and the answer is bad". Readers route on this: the first
#: is a host condition worth retrying, the second is a soundness red.
WALL_TAG = "kernel-incomplete: "
#: EX_TEMPFAIL. The gate exits this when the kernel pass could not be completed:
#: no soundness verdict was produced, and CI must not be read as either green or
#: red on the corpus. The estate already uses 75 for "queue and retry".
EX_TEMPFAIL = 75

#: Kinds the kernel can be asked about with `#print axioms`.
KERNEL_KINDS = ("theorem", "lemma")

#: All declaration kinds the census counts.
DECL_KINDS = KERNEL_KINDS + (
    "def",
    "abbrev",
    "structure",
    "class",
    "instance",
    "axiom",
    "opaque",
)

MODIFIERS = ("private", "protected", "noncomputable", "partial", "unsafe", "meta")

#: Bodies that compile but prove nothing (CLAUDE.md hard rule 2). Detection is
#: line-local: `:= True` on a theorem line, or a theorem line ending in `:=`
#: with one of these tokens as the first token of the next line.
PLACEHOLDER_BODIES = ("True", "PUnit", "trivial", "⊥")

# --------------------------------------------------------------------------
# Comment / string stripping
# --------------------------------------------------------------------------


def strip_comments(text):
    """Blank out Lean comments and string literals, keeping offsets intact.

    Lean block comments ``/- ... -/`` nest and doc comments ``/-- ... -/`` use
    the same closer, so a depth counter is required.  ``--`` runs to end of
    line.  String literals (including ``#"..."#`` raw strings and
    ``#[[...]]#``) and char literals are blanked as well: a ``sorry`` written
    inside a string is not a tactic.

    The result has the same length and the same newline positions as the
    input, so an index maps to the same line number in the original source.
    """
    out = list(text)
    i, n = 0, len(text)
    block_depth = 0
    while i < n:
        ch = text[i]
        nxt = text[i + 1] if i + 1 < n else ""
        if block_depth:
            if ch == "/" and nxt == "-":
                block_depth += 1
                out[i] = out[i + 1] = " "
                i += 2
                continue
            if ch == "-" and nxt == "/":
                block_depth -= 1
                out[i] = out[i + 1] = " "
                i += 2
                continue
            if ch != "\n":
                out[i] = " "
            i += 1
            continue
        if ch == "/" and nxt == "-":
            block_depth += 1
            out[i] = out[i + 1] = " "
            i += 2
            continue
        if ch == "-" and nxt == "-":
            while i < n and text[i] != "\n":
                out[i] = " "
                i += 1
            continue
        if ch == "#":
            j = i
            while j < n and text[j] == "#":
                j += 1
            hashes = j - i
            if hashes and text[j:j + 2] == "[[":
                close = text.find("]]" + "#" * hashes, j + 2)
                if close != -1:
                    _blank(out, i, close + 2 + hashes)
                    i = close + 2 + hashes
                    continue
            if hashes and j < n and text[j] == '"':
                close = _find_raw_string_end(text, j + 1, "#" * hashes)
                if close != -1:
                    _blank(out, i, close + hashes)
                    i = close + hashes
                    continue
            i += 1
            continue
        if ch == '"':
            close = _find_string_end(text, i + 1)
            if close == -1:
                i += 1
                continue
            _blank(out, i, close + 1)
            i = close + 1
            continue
        if ch == "'":
            close = _find_char_end(text, i + 1)
            if close != -1:
                _blank(out, i, close + 1)
                i = close + 1
                continue
            i += 1
            continue
        i += 1
    return "".join(out)


def _blank(out, start, stop):
    for k in range(start, min(stop, len(out))):
        if out[k] != "\n":
            out[k] = " "


def _find_string_end(text, start):
    i, n = start, len(text)
    while i < n:
        if text[i] == "\\":
            i += 2
            continue
        if text[i] == '"':
            return i
        i += 1
    return -1


def _find_raw_string_end(text, start, term):
    """Index of the closing quote of a `#`*n delimited raw string, or -1."""
    i, n = start, len(text)
    while i < n:
        if text[i] == '"' and text[i:i + len(term)] == term:
            return i
        i += 1
    return -1


def _find_char_end(text, start):
    i, n = start, len(text)
    if i >= n:
        return -1
    if text[i] == "\\":
        i += 2
        return i if i < n and text[i] == "'" else -1
    while i < n:
        if text[i] == "'":
            return i
        if text[i] == "\n":
            return -1
        i += 1
    return -1


# --------------------------------------------------------------------------
# Token scanning
# --------------------------------------------------------------------------

_NAME_STOP = set(" \t\r\n([{:,|;\"'")


def _read_token(text, i):
    j, n = i, len(text)
    while j < n and text[j] not in _NAME_STOP:
        j += 1
    return text[i:j], j


def token_hits(line, word):
    """Columns where `word` occurs in `line` as a standalone Lean token."""
    hits = []
    for m in re.finditer(re.escape(word), line):
        s, e = m.start(), m.end()
        before = line[s - 1] if s > 0 else " "
        after = line[e] if e < len(line) else " "
        if before.isalnum() or before in "_'.":
            continue
        if after.isalnum() or after in "_'.":
            continue
        hits.append(s)
    return hits


class Decl(object):
    __slots__ = ("kind", "name", "full", "line", "file", "private")

    def __init__(self, kind, name, full, line, file, private):
        self.kind = kind
        self.name = name
        self.full = full
        self.line = line
        self.file = file
        self.private = private


class FileScan(object):
    def __init__(self, rel):
        self.rel = rel
        self.decls = []
        self.namespaces = set()
        self.sorry = []
        self.native_decide = []
        self.decide = []
        self.sorryax = []
        self.axioms = []
        self.placeholders = []
        self.print_axioms = 0
        self.extern = 0


_MOD_RE = re.compile(r"^(%s)\s+" % "|".join(MODIFIERS))
_KIND_RE = re.compile(r"^(%s)\b\s*" % "|".join(DECL_KINDS))
_NS_RE = re.compile(r"^namespace\s+(\S+)\s*$")
_END_RE = re.compile(r"^end\s+(\S+)?\s*$")
_ASSIGN_BODY_RE = re.compile(r":=\s*(\S+)")


def scan_source(rel, raw):
    """Scan one Lean file: comments stripped first, then namespaces and bans."""
    code = strip_comments(raw)
    scan = FileScan(rel)
    stack = []
    pending_body = False
    for line_no, line in enumerate(code.splitlines(), start=1):
        body = line.strip()
        if not body:
            continue
        if pending_body:
            # a theorem written as `theorem foo : T :=` with the body on the
            # next line: still the same claim, still checked
            pending_body = False
            if body.split(None, 1)[0].rstrip(",;)]}") in PLACEHOLDER_BODIES:
                scan.placeholders.append(line_no)
        _collect_bans(scan, body, line_no)
        head = body
        mods = []
        while True:
            m = _MOD_RE.match(head)
            if not m:
                break
            mods.append(m.group(1))
            head = head[m.end():].lstrip()
        m = _NS_RE.match(head)
        if m:
            stack.append(m.group(1))
            for k in range(1, len(stack) + 1):
                scan.namespaces.add(".".join(stack[:k]))
            continue
        m = _END_RE.match(head)
        if m:
            leaf = (m.group(1) or "").split(".")[-1]
            for k in range(len(stack) - 1, -1, -1):
                if stack[k].split(".")[-1] == leaf:
                    del stack[k:]
                    break
            else:
                if leaf and stack and stack[-1].split(".")[-1] == leaf:
                    stack.pop()
                elif stack:
                    stack.pop()
            continue
        m = _KIND_RE.match(head)
        if not m:
            continue
        kind = m.group(1)
        name, _ = _read_token(head, m.end())
        if name.startswith(":") or not name or kind in ("instance", "example"):
            name = ""
        if kind == "axiom":
            scan.axioms.append((name or "<anonymous>", line_no))
        full = ".".join([p for p in stack + [name] if p]) if name else ""
        scan.decls.append(Decl(kind, name, full, line_no, rel, "private" in mods))
        if kind in KERNEL_KINDS and body.rstrip().endswith(":="):
            pending_body = True
    return scan, code


def _collect_bans(scan, body, line_no):
    """Record banned tokens found in one already-stripped line."""
    for word, bucket in (
        ("native_decide", "native_decide"),
        ("sorryAx", "sorryax"),
        ("sorry", "sorry"),
        ("decide", "decide"),
    ):
        # token boundaries mean `decide` cannot match the tail of
        # `native_decide`, and `sorry` cannot match inside `sorryAx`
        for col in token_hits(body, word):
            getattr(scan, bucket).append(line_no)
    if body.startswith("#print axioms"):
        scan.print_axioms += 1
    if "@[extern" in body or "@[implemented_by" in body:
        scan.extern += 1
    if _is_proof_head(body):
        m = _ASSIGN_BODY_RE.search(body)
        if m and m.group(1).rstrip(",;)]}").strip() in PLACEHOLDER_BODIES:
            scan.placeholders.append(line_no)


def _is_proof_head(body):
    return bool(re.match(r"^(%s\s+)*(%s)\b" % ("|".join(MODIFIERS), "|".join(KERNEL_KINDS)), body))


def discover_lean_files(root):
    files = []
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = [d for d in dirnames if d not in (".lake", ".git", "node_modules", ".venv")]
        for fn in filenames:
            if fn.endswith(".lean"):
                files.append(os.path.join(dirpath, fn))
    return sorted(files)


def census(root):
    """All static measurements, before anyone claims them in prose."""
    files = discover_lean_files(root)
    scans = {}
    for path in files:
        rel = os.path.relpath(path, root).replace(os.sep, "/")
        with open(path, "r", encoding="utf-8") as fh:
            raw = fh.read()
        scans[rel], _code = scan_source(rel, raw)
    decls = []
    for rel in sorted(scans):
        decls.extend(scans[rel].decls)
    counts = {
        "lean_files": len(files),
        "theorem_count": sum(1 for d in decls if d.kind == "theorem"),
        "lemma_count": sum(1 for d in decls if d.kind == "lemma"),
        "other_decl_count": sum(1 for d in decls if d.kind not in KERNEL_KINDS),
        "private_decls": sum(1 for d in decls if d.private),
        "public_kernel_decls": sum(
            1 for d in decls if d.kind in KERNEL_KINDS and not d.private and d.full
        ),
        "sorry_in_code": sum(len(s.sorry) for s in scans.values()),
        "native_decide_in_code": sum(len(s.native_decide) for s in scans.values()),
        "user_axioms": sum(len(s.axioms) for s in scans.values()),
        "placeholders": sum(len(s.placeholders) for s in scans.values()),
    }
    names = set()
    for d in decls:
        if d.full:
            names.add(d.full)
            names.add(d.name)
    detail = {
        "sorry_lines": [(rel, ln) for rel, s in sorted(scans.items()) for ln in s.sorry],
        "native_decide_lines": [(rel, ln) for rel, s in sorted(scans.items()) for ln in s.native_decide],
        "decide_lines": [(rel, ln) for rel, s in sorted(scans.items()) for ln in s.decide],
        "sorryax_lines": [(rel, ln) for rel, s in sorted(scans.items()) for ln in s.sorryax],
        "axiom_lines": [(rel, nm, ln) for rel, s in sorted(scans.items()) for nm, ln in s.axioms],
        "placeholder_lines": [(rel, ln) for rel, s in sorted(scans.items()) for ln in s.placeholders],
        "print_axioms_in_sources": sum(s.print_axioms for s in scans.values()),
        "extern_decls": sum(s.extern for s in scans.values()),
    }
    return {
        "root": root,
        "files": files,
        "scans": scans,
        "decls": decls,
        "names": names,
        "namespaces": {ns for s in scans.values() for ns in s.namespaces},
        "counts": counts,
        "public_kernel": [d for d in decls if d.kind in KERNEL_KINDS and not d.private and d.full],
        "detail": detail,
    }


# --------------------------------------------------------------------------
# Gates
# --------------------------------------------------------------------------


def static_violations(root, c):
    v = []
    counts = c["counts"]
    detail = c["detail"]
    if not counts["lean_files"]:
        return ["no .lean files under %s — the gate would be certifying nothing" % root]
    for rel, ln in detail["sorry_lines"]:
        v.append("%s:%d: `sorry` in executable code" % (rel, ln))
    for rel, ln in detail["sorryax_lines"]:
        v.append("%s:%d: `sorryAx` term — an admitted proof spelled out" % (rel, ln))
    for rel, ln in detail["native_decide_lines"]:
        v.append("%s:%d: `native_decide` is banned (CLAUDE.md hard rule 6)" % (rel, ln))
    for rel, nm, ln in detail["axiom_lines"]:
        v.append("%s:%d: user `axiom` declaration `%s` (CLAUDE.md hard rule 1)" % (rel, ln, nm))
    for rel, ln in detail["placeholder_lines"]:
        v.append("%s:%d: TN placeholder body on a theorem (CLAUDE.md hard rule 2)" % (rel, ln))
    return v


#: Vocabulary that is Lean/Mathlib plumbing rather than a citation of this
#: corpus, so a README mention of it is not a soundness claim about a name.
NON_CITATION_WORDS = frozenset(ALLOWED_AXIOMS) | frozenset((
    "sorry",
    "sorryAx",
    "native_decide",
    "decide",
    "axiom",
    "theorem",
    "lemma",
    "def",
    "structure",
    "instance",
    "namespace",
    "lake",
    "lean",
    "Mathlib",
))

#: Top-level name components owned by a dependency, not by this corpus.
EXTERNAL_ROOTS = ("Mathlib", "Lean", "Std", "Init", "Batteries", "Aesop")

_CITATION_SHAPE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*\Z")
_FILE_SUFFIX = re.compile(r"\.(md|lean|py|json|yml|yaml|toml|txt)\Z")


def readme_citations(readme_text):
    """Corpus names README.md cites as theorem-level claims.

    Anything backticked that is identifier-shaped and carries a `_` or a `.`
    is treated as a citation: in this corpus those are exactly the shapes
    theorem, lemma, calibration-field and namespace-qualified names have. A
    citation that no longer resolves means the README (and the blog page built
    from it) is asserting a receipt the compiler no longer issues.
    """
    cites = []
    for tok in re.findall(r"`([^`\n]+)`", readme_text):
        if not _CITATION_SHAPE.match(tok):
            continue
        if "/" in tok or tok.startswith(".") or tok.endswith("."):
            continue
        if _FILE_SUFFIX.search(tok):
            continue
        if tok in NON_CITATION_WORDS or tok in CENSUS_KEYS:
            continue
        if tok.split(".")[0] in EXTERNAL_ROOTS:
            continue
        if "_" not in tok and "." not in tok:
            continue
        if tok not in cites:
            cites.append(tok)
    m = re.search(r"#print axioms\s+([A-Za-z_][A-Za-z0-9_.]*)", readme_text)
    if m and m.group(1) not in cites:
        cites.append(m.group(1))
    return cites


def typed_names(c):
    """Every identifier the corpus itself spells as `name : Type`.

    Structure fields and binders are what the calibration prose cites
    (`H_min`, `L_non`), so they belong in the resolution universe even though
    they are not declarations.
    """
    names = set()
    for path in c["files"]:
        with open(path, "r", encoding="utf-8") as fh:
            code = strip_comments(fh.read())
        for m in re.finditer(r"\b([A-Za-z_][A-Za-z0-9_]*)\s*:", code):
            names.add(m.group(1))
    return names


def citation_universe(c, extra=None):
    u = set(c["names"])
    u |= typed_names(c)
    u |= set(c.get("namespaces", ()))
    if extra:
        u |= set(extra)
    return u


def citation_resolves(tok, universe, full_names):
    """Does a README citation name a live thing in this corpus?

    An undotted citation may be a declaration leaf or a typed name. A dotted
    one must match the tail of a real full name, so `FirmCashFlow.margin_...`
    resolves against `Economy.FirmCashFlow.margin_...` while a made-up
    namespace prefix does not.
    """
    if tok in universe:
        return True
    if "." not in tok:
        return False
    parts = tok.split(".")
    for nm in full_names:
        nm_parts = nm.split(".")
        if len(nm_parts) >= len(parts) and nm_parts[-len(parts):] == parts:
            return True
    return False


def parse_census_block(text):
    """The dict inside the audit-census block, or None when the block is absent."""
    if CENSUS_BEGIN not in text or CENSUS_END not in text:
        return None
    seg = text.split(CENSUS_BEGIN, 1)[1].split(CENSUS_END, 1)[0]
    out = {}
    for line in seg.splitlines():
        line = line.strip().strip("`").strip()
        if ":" not in line or line.startswith("#"):
            continue
        key, val = line.split(":", 1)
        key = key.strip()
        # a key the gate does not know is still a claim the README is making,
        # so it is returned and reported, not silently dropped
        if re.match(r"[A-Za-z_][A-Za-z0-9_]*\Z", key):
            out[key] = val.strip()
    return out


def readme_expected(c, cites):
    exp = dict(c["counts"])
    exp["theorem_citations"] = len(cites)
    exp["allowed_axioms"] = ", ".join(ALLOWED_AXIOMS)
    return exp


def readme_violations(root, c, readme_text=None):
    path = os.path.join(root, "README.md")
    if readme_text is None:
        if not os.path.isfile(path):
            return ["README.md is missing — its soundness claims cannot be audited"]
        with open(path, "r", encoding="utf-8") as fh:
            readme_text = fh.read()
    block = parse_census_block(readme_text)
    if block is None:
        return [
            "README.md has no `%s` census block: its soundness claims are unpinned "
            "prose that no CI step can check" % CENSUS_BEGIN
        ]
    cites = readme_citations(readme_text)
    exp = readme_expected(c, cites)
    universe = citation_universe(c)
    full_names = sorted({d.full for d in c["decls"] if d.full})
    v = []
    for key in CENSUS_KEYS:
        if key not in block:
            v.append("README census is missing key `%s`" % key)
        elif block[key] != str(exp[key]):
            v.append("README census `%s` says %r, the corpus measures %r" % (key, block[key], exp[key]))
    for extra in sorted(set(block) - set(CENSUS_KEYS)):
        v.append("README census carries unknown key `%s` which the gate cannot check" % extra)
    for name in cites:
        if citation_resolves(name, universe, full_names):
            continue
        v.append("README cites `%s`, but no such declaration exists in the corpus" % name)
    if not cites:
        v.append("README cites no theorems at all — the receipts section is gone")
    return v


# --------------------------------------------------------------------------
# Forecast-table parity
# --------------------------------------------------------------------------
#
# `forecasts/forecast_table.md` is a published carrier: its receipts cite
# declarations by file AND line. Name-only citations (what the README uses)
# drift only when a declaration is renamed; line citations drift when ANY
# line is inserted above the target, which is every ordinary edit. Measured
# at d5fdebc: all thirteen numbered citations in the table pointed at prose
# or unrelated tactic lines, and no gate noticed, because nothing checked
# this file. The parity below decides each citation against the compiler-
# adjacent census (declaration file + line), never against a text guess.

FORECAST_REL = os.path.join("forecasts", "forecast_table.md")
_FORECAST_CITE_RE = re.compile(r"`(Economy/[A-Za-z0-9_]+\.lean):([0-9]+)`")
_MD_TOKEN_RE = re.compile(r"`([A-Za-z_][A-Za-z0-9_.]*)`")
_MD_PARAGRAPH_STOP_RE = re.compile(r"^\s*$|^#|^\s*\|")


def forecast_citation_contexts(md_text):
    """Every numbered citation in the table, with the names around it.

    Returns [(md_line, rel_file, cited_line, [tokens, ...]), ...]. Tokens
    are identifier-shaped backticked names: those on the citation's own
    line before the citation come first — the Receipts bullets cite their
    leftmost name (`ModelCalibration` before the `gK`/`costSavings` field
    mentions) — and when a wrapped citation carries none on its own line,
    the walk goes up to the nearest line with any tokens, stopping at a
    blank line, heading, table row, or another citation so context cannot
    leak between receipts.
    """
    lines = md_text.splitlines()
    out = []
    for i, line in enumerate(lines):
        for m in _FORECAST_CITE_RE.finditer(line):
            toks = [t for t in _MD_TOKEN_RE.findall(line[:m.start()])
                    if "/" not in t and not t.endswith(".lean")]
            j = i - 1
            while not toks and j >= 0 and not _MD_PARAGRAPH_STOP_RE.search(lines[j]) \
                    and not _FORECAST_CITE_RE.search(lines[j]):
                toks = [t for t in _MD_TOKEN_RE.findall(lines[j])
                        if "/" not in t and not t.endswith(".lean")]
                j -= 1
            out.append((i + 1, m.group(1), int(m.group(2)), toks))
    return out


def forecast_violations(root, c, md_text=None):
    """Do the published forecast table's file:line receipts still point true?

    A citation passes when the census measures one of its context names as
    a declaration on the cited line of the cited file. Every failure says
    where the named declaration actually lives, because that is the repair
    the next editor needs. An absent table is not a violation: the gate
    pins citations the repository publishes, and certifies nothing about
    a carrier it has removed.
    """
    path = os.path.join(root, FORECAST_REL)
    if md_text is None:
        if not os.path.isfile(path):
            return []
        with open(path, "r", encoding="utf-8") as fh:
            md_text = fh.read()
    live = {}   # (file, line) -> names declared there
    where = {}  # name -> [(file, line), ...]
    for d in c["decls"]:
        here = live.setdefault((d.file, d.line), set())
        if d.name:
            here.add(d.name)
            where.setdefault(d.name, []).append((d.file, d.line))
        if d.full:
            here.add(d.full)
            where.setdefault(d.full, []).append((d.file, d.line))
    files = {d.file for d in c["decls"]}
    v = []
    for md_line, rel, cited, toks in forecast_citation_contexts(md_text):
        if rel not in files:
            v.append("%s:%d cites %s, which holds no Lean declarations"
                     % (FORECAST_REL, md_line, rel))
            continue
        if any(t in live.get((rel, cited), ()) for t in toks):
            continue
        if not toks:
            v.append("%s:%d cites %s:%d with no named declaration in its context"
                     % (FORECAST_REL, md_line, rel, cited))
            continue
        home = None
        for t in toks:
            homes = where.get(t)
            if not homes:
                continue
            same_file = [h for h in homes if h[0] == rel]
            home = (t, same_file[0] if same_file else homes[0])
            break
        if home is None:
            v.append("%s:%d cites %s:%d for `%s`, none of which is a live declaration"
                     % (FORECAST_REL, md_line, rel, cited, "` or `".join(toks)))
            continue
        name, (hfile, hline) = home
        v.append("%s:%d cites `%s` at %s:%d, but the corpus measures it at %s:%d"
                 % (FORECAST_REL, md_line, name, rel, cited, hfile, hline))
    return v


CI_CHECK_TOKENS = (
    ("audit_axioms.py", "the axiom gate never runs in CI"),
    ("--check", "CI does not run the static gate"),
    ("--verify-kernel", "CI never asks the kernel what an axiom profile is"),
)


# Commands whose exit status decides soundness. The shell-shape checks below
# bite on these only: a `|| true` next to a gate command swallows a verdict,
# while the same idiom on a `git fetch` retry is just a retry, and flagging
# that would turn another lane's step into a false red on this gate.
GATE_COMMANDS = (
    "audit_axioms.py",
    "native_decide_census.py",
    "lake build",
    "lake exe cache get",
    "-m unittest",
    "pytest",
    "make proof",
)


def is_gate_step(step):
    return any(marker in step for marker in GATE_COMMANDS)


def ci_path_of(root):
    return os.path.join(root, ".github", "workflows", "ci.yml")


def strip_yaml_comments(text):
    """Drop whole-line YAML/shell comments so prose cannot trip token checks.

    A comment that merely *mentions* `lake exe cache get` must not be mistaken
    for a call of it, so every gate below runs against the comment-free text.
    Kept line-for-line so a violation's line number still matches the file.
    """
    out = []
    for line in text.splitlines(keepends=True):
        stripped = line.lstrip()
        if stripped.startswith("#"):
            out.append("\n" if line.endswith("\n") else "")
        else:
            out.append(line)
    return "".join(out)


def ci_violations(root, text=None):
    path = ci_path_of(root)
    if text is None:
        if not os.path.isfile(path):
            return [".github/workflows/ci.yml is missing — nothing enforces the invariant"]
        with open(path, "r", encoding="utf-8") as fh:
            text = fh.read()
    text = strip_yaml_comments(text)
    v = []
    for token, why in CI_CHECK_TOKENS:
        if token not in text:
            v.append("ci.yml: %s (missing token %r)" % (why, token))
    for m in re.finditer(r"^\s*(.*rm\s+-rf[^\n]*)$", text, re.M):
        stmt = m.group(1).strip()
        if "cache" in stmt or ".lake/packages" in stmt:
            v.append("ci.yml: destructive cache command writes through symlinks: %s" % stmt)
    # `|| true` is only a swallowed verdict when the command it guards is one
    # that decides soundness; `git fetch ... || true` is a retry.
    for num, line in enumerate(text.splitlines(), start=1):
        if re.search(r"\|\|\s*true", line) and is_gate_step(line):
            v.append("ci.yml:%d: `|| true` swallows a gate failure: %s"
                     % (num, line.strip()[:90]))
    if re.search(r"continue-on-error:\s*true", text):
        v.append("ci.yml: continue-on-error makes the audit advisory")
    if "lake exe cache get" in text and not cache_get_guarded(text):
        v.append(
            "ci.yml: `lake exe cache get` runs without a symlink preflight; when "
            ".lake/packages/* are symlinks it writes through into the machine-wide cache"
        )
    # Invisible to every other check here: the cache call lives inside the
    # action, so no preflight written in this file can guard it.
    if "leanprover/lean-action" in text:
        v.append(
            "ci.yml: leanprover/lean-action calls `lake exe cache get` inside "
            "the action, where no preflight in this file can guard it: on this "
            "estate that writes through the machine-wide Mathlib cache, and it "
            "burned the whole job ceiling in run 43527300771. Build in a step "
            "that probes .lake/packages first."
        )
    if "persist-credentials: false" not in text:
        v.append("ci.yml: actions/checkout must not persist credentials")
    if "timeout-minutes" not in text:
        v.append("ci.yml: no timeout-minutes, so a wedged build pins the runner")
    if "--verify-kernel" in text and "--slot-wait" not in text \
            and "--no-slot" not in text:
        v.append(
            "ci.yml: the kernel pass takes no stance on the build slot. On the "
            "estate runner give it --slot-wait, or a host busy with other lanes' "
            "builds makes the gate red for queueing; off-estate, --no-slot says "
            "there is no slot table to ask."
        )
    for step in run_steps(text):
        if not is_gate_step(step):
            continue
        if len(step.strip().splitlines()) > 1 and "set -euo pipefail" not in step:
            first = step.strip().splitlines()[0]
            v.append("ci.yml: multi-line gate step without `set -euo pipefail`, so a "
                     "failing command before the last one is not fatal: %s" % first[:60])
        # Backticks inside double quotes are still command substitution in bash,
        # so a "we are skipping this" message can quietly run the very command
        # the step exists to guard.
        for m in re.finditer(r'"[^"\n]*`[^"\n]*"', step):
            v.append("ci.yml: backticks inside a double-quoted string execute as a "
                     "command: %s" % m.group(0).strip()[:80])

    # A ceiling on the JOB is not a ceiling on a STEP. Cancellation is a
    # job-level act: when run 43547320929's cache step ran past the 45-minute
    # job bound the whole job concluded `cancelled`, every step after it was
    # `skipped`, and the repository had no verdict at all -- the fourth such run
    # in a row. A step that runs a soundness-deciding command must carry its own
    # `timeout-minutes` so it reports its own name and the run keeps the
    # verdicts of the steps that already passed.
    for block in step_blocks(text):
        if not is_gate_step(block):
            continue
        if "timeout-minutes" in block:
            continue
        label = re.search(r"- name:\s*(.+)", block)
        v.append("ci.yml: gate step has no step-level timeout-minutes, so a slow "
                 "command here is cancelled by the job ceiling and discards the "
                 "verdicts of every other step: %s"
                 % (label.group(1).strip()[:70] if label else block.splitlines()[0][:70]))
    # And the kernel pass's third answer must be named in the workflow: a run
    # that could not ask the kernel is a retry, not an indictment of 80 theorems.
    for block in step_blocks(text):
        if "audit_axioms.py" not in block or "--verify-kernel" not in block:
            continue
        if "-eq 75" not in block and "-eq ${rc}" not in block \
                and "eq 75" not in block:
            v.append("ci.yml: the kernel gate does not name exit 75. A kernel pass "
                     "that could not ask every declaration on a busy host is "
                     "incomplete, and a reader must be able to tell that apart "
                     "from the kernel answering and finding something wrong.")
    return v


def step_blocks(text):
    """The YAML step blocks, as lists of lines, in file order.

    Deliberately textual rather than a YAML parse: this gate must run on a host
    with no pyyaml, and the shape it cares about (`- name:` / `- uses:` at the
    step indent, until the next step) is stable. The returned blocks include
    each step's own keys, which is where `timeout-minutes` for a step lives.
    """
    blocks = []
    cur = None
    for line in text.splitlines():
        if re.match(r"^      - (name|uses):", line):
            if cur:
                blocks.append(cur)
            cur = [line]
        elif cur is not None:
            if re.match(r"^    [a-zA-Z_]+:", line) or re.match(r"^  \S", line):
                blocks.append(cur)
                cur = None
            else:
                cur.append(line)
    if cur:
        blocks.append(cur)
    return ["\n".join(b) for b in blocks]


def cache_get_guarded(text):
    """True when no `lake exe cache get` can run against a symlinked prefix.

    Two shapes are protected. The old one: the step itself probes the package
    dirs for symlinks (`-L` plus a LINKED decision) and seeds only on a real
    directory. The new one: the step first runs scripts/warm_cache.py, whose
    contract is to bind the estate generation and REFUSE when it cannot prove
    the bind safe, so the fetch sits on the refusal branch and runs only where
    nothing is symlinked. Anything else is unprotected.

    A fetch living outside any step body is also unprotected: it would be a
    top-level key or a comment we failed to see, and guessing is not a guard.
    """
    blocks = step_blocks(text)
    for block in blocks:
        if "lake exe cache get" not in block:
            continue
        upper = block.upper()
        probed = re.search(r"\[\s*-L\s", block) and "LINKED" in upper
        bound = "WARM_CACHE.PY" in upper
        if not (probed or bound):
            return False
    outside = sum(block.count("lake exe cache get") for block in blocks)
    return outside == len(re.findall(r"lake exe cache get", text))


def run_steps(text):
    return re.findall(r"run:\s*\|\n((?:[ \t]+[^\n]*\n)+)", text)


# --------------------------------------------------------------------------
# Kernel verification
# --------------------------------------------------------------------------

AXIOMS_SUFFIX = " depends on axioms:"
NOAX_SUFFIX = " does not depend on any axioms"


def build_probe_source(names, import_line="import Economy"):
    return "%s\n" % import_line + "".join("#print axioms %s\n" % nm for nm in names)


def _norm_name(s):
    """Kernel-printed declaration name -> the name we asked about.

    Lean 4.35 prints the declaration name in single quotes
    (`'Economy.foo' depends on axioms: [...]`); older revisions print it bare.
    No Lean identifier can contain an apostrophe, so stripping the pair is safe.
    """
    return s.strip().strip("'").strip()


def parse_probe_output(output):
    """Split compiler output into (found profiles, unknown names, error lines)."""
    found = {}
    unknown = []
    errors = []
    for line in output.splitlines():
        s = line.strip()
        if AXIOMS_SUFFIX in s:
            name, rest = s.split(AXIOMS_SUFFIX, 1)
            inner = rest.strip().strip("[]").strip()
            found[_norm_name(name)] = [a.strip() for a in inner.split(",") if a.strip()]
        elif s.endswith(NOAX_SUFFIX):
            found[_norm_name(s[: -len(NOAX_SUFFIX)])] = []
            continue
        else:
            m = re.search(r"unknown identifier '([^']+)'", s)
            if m:
                unknown.append(m.group(1))
            elif "error" in s.lower():
                errors.append(s)
    return found, unknown, errors


def chunked(seq, size):
    size = max(1, size)
    for i in range(0, len(seq), size):
        yield seq[i:i + size]


class SlotRefused(RuntimeError):
    """The host build slot said no, or could not be consulted.

    Running the probe anyway would be the unfair option: an unleased
    `lake env lean` fans out per-core `lean` children that no gated caller can
    preempt, and the gated `lake build` owners get rc=76 instead of a CPU.
    """


class BuildSlot:
    """A lease on `lean-build-slot.py`, taken per probe batch.

    `lake` only consults the slot table for `lake build`; `lake env lean`
    bypasses it entirely. So the kernel pass asks for a slot before each batch
    and releases it on the way out, which lets other lanes' builds interleave
    between our batches instead of queueing behind the whole audit.

    Three honest fallbacks, each announced in the log: the slot script is not
    on this host (a clean runner), the estate already holds one for us
    (`KAGAMI_LEAN_BUILD_SLOT_HELD` — taking a second would deadlock our own
    tree), or `--no-slot` was passed. In all three the batch is still bounded
    by its own wall clock, so an unleased probe can never run indefinitely.
    """

    def __init__(self, root, wait=None, log=None, script=None, locks_dir=None,
                 pid=None, enabled=True):
        self.root = root
        self.wait = int(SLOT_WAIT if wait is None else wait)
        self.log = log or (lambda msg: None)
        self.script = script or SLOT_SCRIPT
        self.locks_dir = locks_dir or os.environ.get(LOCKS_DIR_ENV) or DEFAULT_LOCKS_DIR
        self.pid = os.getpid() if pid is None else int(pid)
        # An explicit `script` means the caller knows what it is asking for
        # (the unit suite points at a fake adapter). The estate switch and
        # --no-slot turn off the default adapter, which is the one that would
        # otherwise queue real builds behind a test.
        self.enabled = enabled and not (
            script is None and os.environ.get("ECONOMY_AUDIT_NO_SLOT"))
        self.held = False
        self.note = None

    def __enter__(self):
        self.acquire()
        return self

    def __exit__(self, *exc_info):
        self.release()
        return False

    def acquire(self):
        if not self.enabled:
            self.note = "no slot lease (--no-slot): batch bounded by its wall clock"
            self.log("  " + self.note)
            return
        if os.environ.get(SLOT_HELD_ENV):
            self.note = "slot already held by our parent (%s): pass-through" % SLOT_HELD_ENV
            self.log("  " + self.note)
            return
        if not os.path.isfile(self.script):
            self.note = "no %s here: batch bounded by its wall clock" % self.script
            self.log("  " + self.note)
            return
        cmd = [sys.executable, self.script, "acquire", "--dir", self.locks_dir,
               "--project", self.root, "--wait", str(self.wait), "--pid", str(self.pid)]
        try:
            proc = subprocess.run(cmd, capture_output=True, text=True,
                                  timeout=self.wait + 120)
        except (OSError, subprocess.TimeoutExpired) as exc:
            raise SlotRefused("cannot run %s: %s" % (self.script, exc))
        out = (proc.stdout or "").strip().splitlines()
        line = out[-1] if out else (proc.stderr or "").strip()[:200]
        if proc.returncode == 75:
            raise SlotRefused("host build slot refused us after %ds (%s)"
                              % (self.wait, line))
        if proc.returncode != 0:
            raise SlotRefused("host build slot could not be consulted (rc=%d: %s)"
                              % (proc.returncode, line))
        self.held = "slot=-1" not in line  # -1 means the slot leg is disabled
        self.note = "build slot %s" % line
        self.log("  " + self.note)

    def release(self):
        if not self.held:
            return
        self.held = False
        cmd = [sys.executable, self.script, "release", "--dir", self.locks_dir,
               "--pid", str(self.pid)]
        try:
            subprocess.run(cmd, capture_output=True, text=True, timeout=60)
        except (OSError, subprocess.TimeoutExpired):
            # The lease is reclaimable by proof-of-death, so this is pressure,
            # not a leak: the next acquirer sees our pid gone and takes it.
            self.log("  build slot release unconfirmed; the next acquirer reclaims it")


def _timeout_wrapper():
    """`timeout(1)` if it exists, else None (subprocess then bounds the run)."""
    for name in ("timeout", "gtimeout"):
        path = shutil.which(name)
        if path:
            return [path]
    return []


def run_kernel_audit(root, names, batch=80, timeout=None, log=None, lake=None,
                     tmpdir=None, extra_opts=None, slot_wait=None, use_slot=True,
                     slot_script=None, status=None):
    """Ask the kernel for every axiom profile. Returns (found, unknown, errors, notes).

    Batches are separate compiler runs: a Lean parse error stops the compiler
    reporting the rest of a file, so one bad probe line must not be able to
    silence 260 answers.

    Each batch runs under `timeout(1)` and, on this estate, under a
    `lean-build-slot.py` lease taken per batch and released between batches:
    `lake env lean` is invisible to the slot cap, and an unleased probe
    competes with every admitted `lake build` on the host.

    A batch that reaches its wall bound is not evidence about the corpus. It is
    halved and retried, down to WALL_SPLIT_FLOOR, because the honest reading of
    a slow batch on a busy host is "these declarations were not asked yet", not
    "these theorems are unsound". Whatever is left unanswered when splitting is
    exhausted is reported through `status` — `status["lost"]` (declarations the
    kernel never answered), `status["walls"]` (one line per wall) and
    `status["splits"]` (how often the host was too slow) — and the caller turns
    that into EX_TEMPFAIL, a retry, rather than a soundness red.
    """
    log = log or (lambda msg: None)
    if status is None:
        status = {}
    status.setdefault("lost", [])
    status.setdefault("walls", [])
    status.setdefault("splits", 0)
    lake = lake or shutil.which("lake")
    if not lake:
        raise RuntimeError("lake not on PATH")
    if not os.path.isfile(lake):
        raise RuntimeError("lake %s does not exist" % lake)
    opts = list(extra_opts if extra_opts is not None else ["-D", "autoImplicit=false"])
    wrapper = _timeout_wrapper()
    found = {}
    unknown = []
    errors = []
    notes = []
    own_tmp = tmpdir is None
    tmpdir = tmpdir or tempfile.mkdtemp(prefix="economy-axiom-audit-")
    try:
        queue = [[list(chunk), 0] for chunk in chunked(names, batch)]
        seq = 0
        while queue:
            chunk, depth = queue.pop(0)
            seq += 1
            probe = os.path.join(tmpdir, "AxiomProbe%d.lean" % seq)
            with open(probe, "w", encoding="utf-8") as fh:
                fh.write(build_probe_source(chunk))
            lease = BuildSlot(root, wait=slot_wait, log=log, enabled=use_slot,
                              script=slot_script)
            walled = None
            with lease:
                bound = timeout if timeout is not None else (
                    PROBE_LEASED_S if lease.held else PROBE_UNLEASED_S)
                argv = (list(wrapper) + [str(bound)] if wrapper else []) + \
                    [lake, "-d", root, "env", "lean"] + opts + [probe]
                log("  probe batch #%d (%d declarations, <=%ds%s%s)"
                    % (seq, len(chunk), bound,
                       ", slot held" if lease.held else "",
                       ", split depth %d" % depth if depth else ""))
                try:
                    proc = subprocess.run(argv, cwd=root, capture_output=True,
                                          text=True, timeout=bound + 60)
                except subprocess.TimeoutExpired:
                    walled = "probe batch #%d timed out in the harness after %ds" \
                             % (seq, bound + 60)
                    tail = ""
                except OSError as exc:
                    raise RuntimeError("cannot run %s: %s" % (argv[0], exc))
                else:
                    if proc.returncode in (124, 137):
                        walled = "probe batch #%d hit its %ds wall bound (rc=%d)" \
                                 % (seq, bound, proc.returncode)
                        tail = (proc.stdout + proc.stderr).strip()[:200]
                if walled is None:
                    out, unk, errs = parse_probe_output(
                        proc.stdout + "\n" + proc.stderr)
                    found.update(out)
                    unknown.extend(unk)
                    errors.extend(errs)
                    if not out and not unk:
                        notes.append(
                            "probe batch #%d produced no axiom profile (rc=%d): %s"
                            % (seq, proc.returncode,
                               (proc.stdout + proc.stderr).strip()[:200]))
            if walled is not None:
                status["walls"].append("%s: %s" % (walled, tail) if tail else walled)
                if len(chunk) > WALL_SPLIT_FLOOR and depth < WALL_SPLIT_DEPTH:
                    mid = len(chunk) // 2
                    queue[:0] = [[chunk[:mid], depth + 1], [chunk[mid:], depth + 1]]
                    status["splits"] += 1
                    log("  %s — %d declarations split into %d+%d and retried"
                        % (walled, len(chunk), mid, len(chunk) - mid))
                    continue
                status["lost"].extend(chunk)
                errors.append("%s%s, and %d declaration(s) remain unverified: %s"
                              % (WALL_TAG, walled, len(chunk),
                                 ", ".join(chunk[:8])))
    finally:
        if own_tmp:
            shutil.rmtree(tmpdir, ignore_errors=True)
    return found, unknown, errors, notes


def kernel_violations(c, found, unknown, errors, notes, lost=()):
    """Soundness verdicts from a kernel pass.

    `lost` is the set of declarations the compiler never answered because its
    batches hit the wall bound. They are NOT violations: `#print axioms` was
    never asked, so there is no evidence either way, and listing them as
    violations would let a busy host demote the corpus with 80 fabricated
    soundness findings. They surface as EX_TEMPFAIL instead, by way of the
    caller, and the gate stays unable to say CLEAN.
    """
    v = []
    allowed = set(ALLOWED_AXIOMS)
    silent = set(lost)
    expected = [d.full for d in c["public_kernel"]]
    for nm in sorted(set(unknown)):
        v.append("kernel: `%s` is not a live declaration (the census is stale)" % nm)
    for nm in expected:
        if nm not in found and nm not in silent:
            v.append("kernel: no `#print axioms` answer for `%s`" % nm)
    for nm in sorted(set(found) - set(expected)):
        v.append("kernel: answered for `%s`, which the static census does not list" % nm)
    for nm in sorted(found):
        for ax in found[nm]:
            if ax not in allowed:
                v.append("kernel: `%s` depends on `%s`, outside the allowed [%s]"
                         % (nm, ax, ", ".join(ALLOWED_AXIOMS)))
    for nt in notes:
        v.append("kernel: %s" % nt)
    for e in [e for e in errors if not e.startswith(WALL_TAG)][:20]:
        v.append("kernel: %s" % e)
    return v


# --------------------------------------------------------------------------
# CLI
# --------------------------------------------------------------------------


def evaluate(root, verify_kernel=False, skip_readme=False, skip_ci=False,
             batch=80, timeout=None, lake=None, log=None,
             slot_wait=None, use_slot=True, slot_script=None):
    """Run the requested gates. Returns (exit_code, census, report).

    0 CLEAN, 1 violations, 2 the gate could not run, and EX_TEMPFAIL (75) when
    the kernel pass ran but a busy host kept it from asking every declaration:
    no verdict either way, so a retry is the only honest next step.
    """
    c = census(root)
    report = {"violations": [], "found": {}, "notes": [], "kernel": False, "rc": 0,
              "kernel_lost": [], "kernel_walls": [], "kernel_splits": 0}
    report["violations"].extend(static_violations(root, c))
    if not skip_readme:
        report["violations"].extend(readme_violations(root, c))
        report["violations"].extend(forecast_violations(root, c))
    if not skip_ci:
        report["violations"].extend(ci_violations(root))
    if verify_kernel:
        status = {}
        try:
            found, unknown, errors, notes = run_kernel_audit(
                root, [d.full for d in c["public_kernel"]], batch=batch,
                timeout=timeout, log=log, lake=lake,
                slot_wait=slot_wait, use_slot=use_slot,
                slot_script=slot_script, status=status)
        except RuntimeError as exc:
            return 2, c, {"violations": ["gate cannot run: %s" % exc],
                          "found": {}, "notes": [], "kernel": False, "rc": 2,
                          "kernel_lost": [], "kernel_walls": [], "kernel_splits": 0}
        report["found"] = found
        report["errors"] = errors
        report["notes"] = notes
        report["kernel"] = True
        report["kernel_lost"] = list(status.get("lost") or [])
        report["kernel_walls"] = list(status.get("walls") or [])
        report["kernel_splits"] = int(status.get("splits") or 0)
        report["violations"].extend(kernel_violations(
            c, found, unknown, errors, notes, lost=report["kernel_lost"]))
    if report["violations"]:
        report["rc"] = 1
    elif report["kernel_lost"]:
        report["rc"] = EX_TEMPFAIL
    else:
        report["rc"] = 0
    return report["rc"], c, report


def emit_json(path, root, c, report):
    found = report["found"]
    payload = {
        "root": root,
        "counts": c["counts"],
        "allowed_axioms": list(ALLOWED_AXIOMS),
        "kernel_verified": bool(report["kernel"]),
        "kernel_declarations_checked": len(found),
        "axiom_profiles": {nm: found[nm] for nm in sorted(found)},
        "distinct_axioms_seen": sorted({ax for v in found.values() for ax in v}),
        "decide_tactic_mentions": len(c["detail"]["decide_lines"]),
        "in_source_print_axioms": c["detail"]["print_axioms_in_sources"],
        "public_kernel_decls": c["counts"]["public_kernel_decls"],
        "violations": report["violations"],
        "notes": report["notes"],
        # A wall bound is a host condition, not a verdict. `clean` means the
        # kernel answered for every declaration it was asked about AND nothing
        # was outside the allowed set; a pass that lost declarations is neither
        # clean nor dirty, it is incomplete, and `kernel_incomplete` says so.
        "kernel_incomplete": bool(report.get("kernel_lost")),
        "kernel_unverified_declarations": sorted(report.get("kernel_lost") or []),
        "kernel_wall_bound_events": list(report.get("kernel_walls") or []),
        "kernel_batches_split": int(report.get("kernel_splits") or 0),
        "clean": (not report["violations"]) and not report.get("kernel_lost"),
        "exit_code": report["rc"],
    }
    with open(path, "w", encoding="utf-8") as fh:
        json.dump(payload, fh, indent=2, sort_keys=True)
        fh.write("\n")


def print_census_block(root):
    """Render the census block for this corpus, with README's citations counted."""
    c = census(root)
    path = os.path.join(root, "README.md")
    text = ""
    if os.path.isfile(path):
        with open(path, "r", encoding="utf-8") as fh:
            text = fh.read()
    exp = readme_expected(c, readme_citations(text))
    lines = ["# %s" % CENSUS_BEGIN]
    lines += ["%s: %s" % (k, exp[k]) for k in CENSUS_KEYS]
    lines.append("# %s" % CENSUS_END)
    return "\n".join(lines)


def write_census_block(root):
    """Refresh the census block in README.md in place.

    This is what makes the numbers derived rather than copied: nothing in the
    repository is hand-typed, and --check fails if the block disagrees with the
    corpus, so a stale claim is a red build instead of a quiet lie.
    """
    path = os.path.join(root, "README.md")
    if not os.path.isfile(path):
        raise SystemExit("README.md not found in %s — refusing to invent its structure" % root)
    with open(path, "r", encoding="utf-8") as fh:
        text = fh.read()
    begin, end = "# " + CENSUS_BEGIN, "# " + CENSUS_END
    if begin not in text or end not in text:
        raise SystemExit(
            "README.md carries no `%s` marker; add the census section first, then refresh"
            % CENSUS_BEGIN)
    block = print_census_block(root)
    new_text = text[:text.index(begin)] + block + text[text.index(end) + len(end):]
    with open(path, "w", encoding="utf-8") as fh:
        fh.write(new_text)
    return block


def main(argv=None):
    ap = argparse.ArgumentParser(description="axiom/sorry gate for the economy corpus")
    ap.add_argument("--root", default=os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
                    help="repository root (default: parent of scripts/)")
    ap.add_argument("--check", action="store_true", help="run the static gate (default)")
    ap.add_argument("--verify-kernel", dest="verify_kernel", action="store_true",
                    help="also query the kernel for every axiom profile")
    ap.add_argument("--json", dest="json_out", help="write a machine-readable report here")
    ap.add_argument("--batch", type=int, default=80, help="declarations per probe file")
    ap.add_argument("--timeout", type=int, default=None,
                    help="wall seconds per probe batch (default: %d with a build"
                         " slot held, %d if the slot lease is unavailable)"
                         % (PROBE_LEASED_S, PROBE_UNLEASED_S))
    ap.add_argument("--slot-wait", dest="slot_wait", type=int, default=None,
                    help="seconds to wait for a build slot (default %d)" % SLOT_WAIT)
    ap.add_argument("--no-slot", dest="use_slot", action="store_false",
                    help="skip the lean-build slot lease (hosts outside the estate)")
    ap.add_argument("--lake", default=None, help="lake executable")
    ap.add_argument("--skip-readme", dest="skip_readme", action="store_true")
    ap.add_argument("--skip-ci", dest="skip_ci", action="store_true")
    ap.add_argument("--quiet", action="store_true")
    ap.add_argument("--print-census", dest="print_census", action="store_true",
                    help="print the README census block for this corpus and exit")
    ap.add_argument("--write-census", dest="write_census", action="store_true",
                    help="refresh the census block in README.md in place and exit")
    args = ap.parse_args(argv)

    root = os.path.abspath(args.root)
    if args.print_census:
        print(print_census_block(root))
        return 0
    if args.write_census:
        print(write_census_block(root))
        return 0

    log = (lambda msg: None) if args.quiet else print
    rc, c, report = evaluate(
        root, verify_kernel=args.verify_kernel, skip_readme=args.skip_readme,
        skip_ci=args.skip_ci, batch=args.batch, timeout=args.timeout,
        lake=args.lake, log=log, slot_wait=args.slot_wait, use_slot=args.use_slot)
    counts = c["counts"]
    if not args.quiet:
        log("economy axiom gate — %s" % root)
        log("  files=%(lean_files)d theorem=%(theorem_count)d lemma=%(lemma_count)d "
            "other=%(other_decl_count)d private=%(private_decls)d" % counts)
        log("  code bans: sorry=%(sorry_in_code)d native_decide=%(native_decide_in_code)d "
            "axiom=%(user_axioms)d placeholder=%(placeholders)d" % counts)
        log("  kernel-checkable public declarations: %(public_kernel_decls)d" % counts)
        if report["found"]:
            seen = sorted({ax for v in report["found"].values() for ax in v})
            log("  kernel verified %d declarations, axioms seen: %s"
                % (len(report["found"]), ", ".join(seen) or "(none)"))
    if args.json_out:
        emit_json(args.json_out, root, c, report)
    if rc == 0:
        if args.verify_kernel:
            print("CLEAN: 0 sorry, 0 native_decide, 0 user axioms; kernel verified every "
                  "public theorem under [%s]" % ", ".join(ALLOWED_AXIOMS))
        else:
            print("CLEAN: 0 sorry, 0 native_decide, 0 user axioms; README census, "
                  "forecast-table citations and CI wiring pinned")
    elif rc == EX_TEMPFAIL:
        lost = report.get("kernel_lost") or []
        print("INCOMPLETE (exit %d): the static gate is clean but the kernel was never "
              "asked for %d of %d public declarations — their probe batches hit the wall "
              "bound even after splitting. This run carries NO soundness verdict: the "
              "corpus is neither certified nor indicted. Retry on a quieter host."
              % (EX_TEMPFAIL, len(lost), counts["public_kernel_decls"]))
        for w in (report.get("kernel_walls") or [])[:5]:
            print("  wall: %s" % w)
        for nm in sorted(lost)[:10]:
            print("  unverified: %s" % nm)
        if len(lost) > 10:
            print("  ... %d more unverified" % (len(lost) - 10))
    else:
        print("VIOLATIONS (%d):" % len(report["violations"]))
        for item in report["violations"]:
            print("  - %s" % item)
        lost = report.get("kernel_lost") or []
        if lost:
            print("  (and %d declaration(s) the kernel never answered — see the "
                  "wall lines above; they are unverified, not violations)" % len(lost))
    if report["notes"] and not args.verify_kernel:
        for nt in report["notes"]:
            print("  note: %s" % nt)
    return rc


if __name__ == "__main__":
    sys.exit(main())
