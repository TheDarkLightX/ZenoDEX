#!/usr/bin/env bash
# Self-check runner for the ZenoDEX Tau ADT/table experiments (nomic-style).
set -u
TAU_BIN="${TAU_BIN:-tau}"
TAU_TIMEOUT="${TAU_TIMEOUT:-600}"
cd "$(dirname "$0")"
strip_ansi() { sed 's/\x1b\[[0-9;?]*[a-zA-Z]//g'; }
fail=0; total=0
for f in exp*.tau; do
  total=$((total+1))
  exp_res=$(grep -m1 '^# EXPECTED-RESULTS:' "$f" | sed 's/^# EXPECTED-RESULTS: *//')
  exp_codes=$(grep -m1 '^# EXPECTED-CODES:' "$f" | sed 's/^# EXPECTED-CODES: *//')
  exp_tf=$(grep -m1 '^# EXPECTED-TF:' "$f" | sed 's/^# EXPECTED-TF: *//')
  out=$(timeout "$TAU_TIMEOUT" "$TAU_BIN" -q < "$f" 2>&1 | strip_ansi)
  printf '%s\n' "$out" > ".out.$f.txt"
  ok=1; detail=""
  if [ -n "$exp_res" ]; then
    act=$(printf '%s\n' "$out" | grep -oE '^%[0-9]+: .*' | sed 's/^%[0-9]*: //' | paste -sd' ' -)
    [ "$act" = "$exp_res" ] || { ok=0; detail="results: got [$act] want [$exp_res]"; }
  fi
  if [ -n "$exp_codes" ]; then
    act=$(printf '%s\n' "$out" | grep -v '^tau> ' | grep -oE 'o0res\[[0-9]+\] *:= *\{? *[0-9]+' | grep -oE '[0-9]+$' | paste -sd, -)
    [ "$act" = "$exp_codes" ] || { ok=0; detail="$detail codes: got [$act] want [$exp_codes]"; }
  fi
  if [ -n "$exp_tf" ]; then
    act=$(printf '%s\n' "$out" | grep -v '^tau> ' | grep -oE 'oent\[[0-9]+\] := [TF01]' | grep -oE '[TF01]$' | sed 's/1/T/;s/0/F/' | paste -sd' ' -)
    [ "$act" = "$exp_tf" ] || { ok=0; detail="$detail tf: got [$act] want [$exp_tf]"; }
  fi
  if [ -z "$exp_res" ] && [ -z "$exp_codes" ] && [ -z "$exp_tf" ]; then echo "INFO  $f (manual contract; output in .out.$f.txt)"; continue; fi
  if [ "$ok" = 1 ]; then echo "PASS  $f"; else echo "FAIL  $f ($detail)"; fail=$((fail+1)); fi
done
echo; echo "$((total-fail))/$total ok"
exit "$fail"
