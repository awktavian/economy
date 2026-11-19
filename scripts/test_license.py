#!/usr/bin/env python3
"""Tests for the repository's license posture — the LICENSE target of the
code map (cleanup score 1.5: "review only when changing build, CI, agent
policy, or repo hygiene").

Hermetic: reads two tracked text files (LICENSE, README.md) and nothing
else; no network, no toolchain. What is under test is repo hygiene, not
legal advice: the MIT grant shipped at the root must stay *the* canonical
MIT text (so GitHub's license detection and any downstream SPDX check
keep reading it as MIT), the copyright line must name the holder this
estate publishes under, and the README "License" section must not claim a
license the root file does not grant. A silent edit to any of these three
turns CI red instead of quietly changing what consumers may do with the
corpus.
"""

import os
import re
import sys
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LICENSE_PATH = os.path.join(ROOT, "LICENSE")
README_PATH = os.path.join(ROOT, "README.md")

# The canonical MIT body from https://opensource.org/license/mit, with the
# year and holder left as placeholders. Line wrapping is part of the text
# that license detectors fingerprint, so it is reproduced exactly.
CANONICAL_MIT = """\
MIT License

Copyright (c) {year} {holder}

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
"""

EXPECTED_HOLDER = "Awkronos, Inc."


def read(path):
    with open(path, encoding="utf-8") as fh:
        return fh.read()


class LicensePosture(unittest.TestCase):

    def test_license_file_is_the_canonical_mit_text(self):
        """LICENSE == MIT template for its declared year and holder.

        Any added, removed or rewrapped clause fails this: the grant a
        consumer can rely on is pinned, not merely eyeballed.
        """
        text = read(LICENSE_PATH)
        match = re.search(
            r"^Copyright \(c\) (\d{4}) (.+)$", text, re.MULTILINE)
        self.assertIsNotNone(
            match, "LICENSE must carry a 'Copyright (c) <year> <holder>' line")
        expected = CANONICAL_MIT.format(year=match.group(1),
                                        holder=match.group(2))
        self.assertEqual(text, expected,
                         "LICENSE drifted from the canonical MIT text")

    def test_copyright_holder_is_the_publisher(self):
        """The named holder stays the estate's publishing entity."""
        text = read(LICENSE_PATH)
        self.assertIn(f"Copyright (c) 2026 {EXPECTED_HOLDER}", text)

    def test_readme_license_section_agrees_with_the_root_file(self):
        """The README 'License' section claims MIT, matching LICENSE.

        A README that says Apache/GPL/proprietary while LICENSE stays MIT
        (or the reverse) is a consumer-visible contradiction; this pins
        the two surfaces to the same word.
        """
        readme = read(README_PATH)
        section = re.search(r"^## License\n(.*?)(?=^## )",
                            readme, re.MULTILINE | re.DOTALL)
        self.assertIsNotNone(section, "README.md lost its '## License' section")
        self.assertIn("MIT", section.group(1),
                      "README 'License' section no longer says MIT")


if __name__ == "__main__":
    unittest.main(verbosity=2)
