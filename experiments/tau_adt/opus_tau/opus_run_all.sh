#!/usr/bin/env bash
# opus_run_all.sh - FAIL-CLOSED self-check runner for the Opus tau corpus.
#
# Differences from nomic_run_all.sh / run_experiments.sh, all of them
# fail-closed hardening:
#
#  1. ENGINE-ERROR GATE. Tau prints "(Error) Failed to translate the formula
#     to cvc5: ..." on STDOUT and still returns a verdict with exit code 0.
#     A runner that only greps '^%N:' therefore scores a degraded decision
#     as PASS. Any '(Error)' line here fails the file.
#  2. EXIT-CODE GATE. A timeout or crash after the expected lines were
#     already printed used to pass; the exit status is now checked.
#  3. EMPTY-ACTUAL GATE. A contract that expects output but matches nothing
#     is a FAIL, not a silent pass on two empty strings.
#  4. EXPECTED-OB. A ledger contract: the ob[] stream reduced to F (empty
#     table) / R (non-empty), which is what the pointwise-revision evidence
#     turns on.
#
#   TAU_BIN=/path/to/tau ./opus_run_all.sh
#   TAU_TIMEOUT=900 ./opus_run_all.sh
set -u
TAU_BIN="${TAU_BIN:-tau}"
TAU_TIMEOUT="${TAU_TIMEOUT:-900}"
cd "$(dirname "$0")"
strip_ansi() { sed 's/\x1b\[[0-9;?]*[a-zA-Z]//g'; }
fail=0; total=0
for f in opus_*.tau; do
  exp_res=$(grep -m1 '^# EXPECTED-RESULTS:' "$f" | sed 's/^# EXPECTED-RESULTS: *//')
  exp_codes=$(grep -m1 '^# EXPECTED-CODES:' "$f" | sed 's/^# EXPECTED-CODES: *//')
  exp_ob=$(grep -m1 '^# EXPECTED-OB:' "$f" | sed 's/^# EXPECTED-OB: *//')
  if [ -z "$exp_res" ] && [ -z "$exp_codes" ] && [ -z "$exp_ob" ]; then
    echo "SKIP  $f (no contract)"; continue
  fi
  total=$((total+1))
  out=$(TAU_BA_COMPONENT_FACTORING=1 timeout "$TAU_TIMEOUT" "$TAU_BIN" -q < "$f" 2>&1 | strip_ansi); rc=$?
  printf '%s\n' "$out" > ".out.$f.txt"
  ok=1; detail=""
  # GATE 1: engine errors are fatal, whatever the verdict lines say.
  # NOTE: the REPL echoes every input line as "tau> ...", so a comment that
  # merely QUOTES an error string would trip this gate. Echoed lines are
  # excluded; only lines the engine itself emitted are scanned.
  if printf '%s\n' "$out" | grep -v '^tau> ' | grep -q '(Error)'; then
    ok=0; detail="ENGINE ERROR (cvc5/translation) - verdict not trusted;"
  fi
  # GATE 2: exit status.
  [ "$rc" = 0 ] || { ok=0; detail="$detail exit=$rc;"; }
  if [ -n "$exp_res" ]; then
    act=$(printf '%s\n' "$out" | grep -oE '^%[0-9]+: .*' | sed 's/^%[0-9]*: //' | paste -sd' ' -)
    [ -n "$act" ] || { ok=0; detail="$detail results: NO %N lines produced;"; }
    [ "$act" = "$exp_res" ] || { ok=0; detail="$detail results: got [$act] want [$exp_res];"; }
  fi
  if [ -n "$exp_codes" ]; then
    act=$(printf '%s\n' "$out" | grep -v '^tau> ' | grep -oE 'o0res\[[0-9]+\] *:= *\{? *[0-9]+' | grep -oE '[0-9]+$' | paste -sd, -)
    [ -n "$act" ] || { ok=0; detail="$detail codes: NO o0res lines produced;"; }
    [ "$act" = "$exp_codes" ] || { ok=0; detail="$detail codes: got [$act] want [$exp_codes];"; }
  fi
  if [ -n "$exp_ob" ]; then
    act=$(printf '%s\n' "$out" | grep -v '^tau> ' | grep -oE '^ob\[[0-9]+\] *:= *.*' \
          | sed -E 's/^ob\[[0-9]+\] *:= *//' | sed -E 's/^F$/F/; s/^(.*[^F].*)$/R/' | paste -sd' ' -)
    [ -n "$act" ] || { ok=0; detail="$detail ob: NO ob lines produced;"; }
    [ "$act" = "$exp_ob" ] || { ok=0; detail="$detail ob: got [$act] want [$exp_ob];"; }
  fi
  if [ "$ok" = 1 ]; then echo "PASS  $f"; else echo "FAIL  $f ($detail)"; fail=$((fail+1)); fi
done
echo; echo "$((total-fail))/$total ok"
exit "$fail"
