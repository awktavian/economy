.PHONY: proof check build clean

proof:
	@~/.claude/scripts/proof-report-refresh.sh --oneline

check:
	@cd /Users/schizodactyl/economy && lake env lean $(FILE) 2>&1 | tail -30

build:
	@cd /Users/schizodactyl/economy && lake exe cache get && lake build Economy

clean:
	@cd /Users/schizodactyl/economy && lake clean
