.PHONY: proof check build clean

proof:
	@cd /Users/schizodactyl/economy && python3 /Users/schizodactyl/projects/kagami/.claude/scripts/proof_report.py --project economy --path .

check:
	@cd /Users/schizodactyl/economy && lake env lean $(FILE) 2>&1 | tail -30

build:
	@cd /Users/schizodactyl/economy && lake exe cache get && lake build Economy

clean:
	@cd /Users/schizodactyl/economy && lake clean
