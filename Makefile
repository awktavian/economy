.PHONY: proof check build clean audit audit-kernel census

proof:
	@~/.claude/scripts/open-math.py verify --project economy --report /tmp/proof-report.json --sidecar /tmp/open_math.json

check:
	@test -n "$(FILE)" || { echo "Usage: make check FILE=path/to/File.lean"; exit 2; }
	@lake env lean "$(FILE)"

build:
	@if [ -L .lake/packages/mathlib ]; then \
	  echo ".lake/packages is symlinked - shared cache is read-only, skipping cache get"; \
	else \
	  lake exe cache get; \
	fi
	@lake build Economy

# Static soundness gate: comment-stripped scans, README census parity, CI wiring.
audit:
	@python3 scripts/audit_axioms.py --check

# Same, plus `#print axioms` for every public theorem through the compiler.
audit-kernel:
	@python3 scripts/audit_axioms.py --check --verify-kernel

# Regenerate the census block in README.md from what the corpus actually contains.
census:
	@python3 scripts/audit_axioms.py --write-census

clean:
	@lake clean
