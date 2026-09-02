#!/usr/bin/env bash
# opus_q.sh - run ONE tau query in a FRESH process (no session name binding).
# usage: opus_q.sh 'n <formula>'
TAU_BIN="${TAU_BIN:-/tmp/claude-1000/-home-trevormoc-Downloads-Autonomous-Tau-DEX/37cec583-0c57-4fc0-844c-9f17c86c9adf/scratchpad/tau-lang-upstream/build-Release/tau}"
TAU_TIMEOUT="${TAU_TIMEOUT:-300}"
printf 'set charvar off\nset maxsplits 1\n%s\n' "$1" \
  | TAU_BA_COMPONENT_FACTORING=1 timeout "$TAU_TIMEOUT" "$TAU_BIN" -q 2>&1 \
  | sed 's/\x1b\[[0-9;?]*[a-zA-Z]//g' | grep -E '^(%[0-9]+:|Error|error|.*[Ee]rror)' | head -20
