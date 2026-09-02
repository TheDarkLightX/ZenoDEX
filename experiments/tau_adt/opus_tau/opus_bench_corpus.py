#!/usr/bin/env python3
"""Bench 3: wall-clock for every file in the corpus, as actually run.

Task 1 of the extended brief: time every query I run. These are whole-file
times (the unit a CI gate would actually enforce), with per-file query counts
so a per-query mean is available.
"""
import json, re, subprocess, sys, time
from pathlib import Path

TAU = sys.argv[1]
DIRS = [Path(sys.argv[2]), Path(sys.argv[3])]
TIMEOUT = 900
rows = []
for d in DIRS:
    for f in sorted(d.glob("*.tau")):
        if f.parent.name == "bench":
            continue
        t0 = time.perf_counter()
        pr = subprocess.run([TAU, "-q"], stdin=f.open(), capture_output=True,
                            text=True, timeout=TIMEOUT,
                            env={**__import__("os").environ, "TAU_BA_COMPONENT_FACTORING": "1"})
        dt = time.perf_counter() - t0
        clean = re.sub(r"\x1b\[[0-9;?]*[a-zA-Z]", "", pr.stdout)
        nq = sum(1 for l in clean.splitlines() if l.strip().startswith("%") and ": " in l)
        nsteps = sum(1 for l in clean.splitlines() if l.startswith("Execution step:"))
        rows.append({"file": f.name, "dir": d.name, "s": round(dt, 3),
                     "queries": nq, "run_steps": nsteps,
                     "per_query": round(dt / nq, 3) if nq else None})
print("| file | dir | seconds | queries | run steps | s/query |")
print("|---|---|---|---|---|---|")
for r in rows:
    print(f"| {r['file']} | {r['dir']} | {r['s']} | {r['queries']} | {r['run_steps']} | {r['per_query'] if r['per_query'] is not None else '-'} |")
Path(__file__).parent.joinpath("bench_corpus.json").write_text(json.dumps(rows, indent=1))
