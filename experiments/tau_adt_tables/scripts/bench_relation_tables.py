#!/usr/bin/env python3
from pathlib import Path
import os, subprocess, time, json, re, sys

root = Path(__file__).resolve().parents[1]
outdir = root / "results" / "relation_bench"
outdir.mkdir(parents=True, exist_ok=True)
tau = os.environ.get("TAU_BIN", "tau")
ansi = re.compile(r"\x1b\[[0-9;]*[A-Za-z]")
rowsizes = [2, 4, 8, 16, 32, 64]
rows = []
for n in rowsizes:
    terms = [f'{{ oiid[t]:bv[8] = {{{i}}}:bv[8] && oqty[t]:bv[16] = {{{i*3+1}}}:bv[16] }}' for i in range(1,n+1)]
    table = " | ".join(terms)
    hit = n
    miss = 255
    spec = f'''set charvar off\nset maxsplits 1\nn ({{ oiid[t]:bv[8] = {{{hit}}}:bv[8] }} & ({table})) != 0\nn ({{ oiid[t]:bv[8] = {{{miss}}}:bv[8] }} & ({table})) = 0\nquit\n'''
    pth = outdir / f"relation_{n}.tau"
    pth.write_text(spec)
    env = os.environ.copy()
    env["TAU_BA_COMPONENT_FACTORING"] = "1"
    t0 = time.perf_counter()
    try:
        p = subprocess.run([tau, "-q", "-X"], input=spec, text=True,
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                           env=env, timeout=120)
        rc = p.returncode
        output = p.stdout
    except subprocess.TimeoutExpired as e:
        rc = 124
        output = (e.stdout or "") + "\nTIMEOUT\n"
    dt = time.perf_counter() - t0
    clean = ansi.sub("", output)
    (outdir / f"relation_{n}.out").write_text(clean)
    answers = re.findall(r"%\d+:\s*(T|F)\b", clean)
    repl_error = "(Error)" in clean or "TIMEOUT" in clean
    ok = rc == 0 and not repl_error and answers == ["T", "T"]
    row = {"rows": n, "seconds": dt, "returncode": rc, "answers": answers,
           "repl_error": repl_error, "ok": ok}
    rows.append(row)
    print(row)
    if rc == 124 or repl_error:
        break

(outdir / "benchmark.json").write_text(json.dumps(rows, indent=2) + "\n")
if not rows or not all(r["ok"] for r in rows):
    sys.exit(1)
