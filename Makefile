.PHONY: proof check build clean

proof:
	@~/.claude/scripts/open-math.py verify --project economy --report /tmp/proof-report.json --sidecar /tmp/open_math.json

check:
	@test -n "$(FILE)" || { echo "Usage: make check FILE=path/to/File.lean"; exit 2; }
	@cd /Users/schizodactyl/economy && lake env lean "$(FILE)"

build:
	@cd /Users/schizodactyl/economy && lake exe cache get && lake build Economy

clean:
	@cd /Users/schizodactyl/economy && lake clean
