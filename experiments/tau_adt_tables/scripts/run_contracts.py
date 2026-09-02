#!/usr/bin/env python3
from pathlib import Path
import os, re, subprocess, sys, time, json

root = Path(__file__).resolve().parents[1]
spec_dir = root / "specs"
results_dir = root / "results"
results_dir.mkdir(exist_ok=True)
tau = os.environ.get("TAU_BIN", "tau")
summary = []

ansi = re.compile(r"\x1b\[[0-9;]*[A-Za-z]")
answer_re = re.compile(r"%\d+:\s*(T|F)\b")
expected_re = re.compile(r"^#\s*EXPECTED-RESULTS:\s*(.*)$", re.M)

for path in sorted(spec_dir.glob("*.tau")):
    text = path.read_text()
    m = expected_re.search(text)
    expected = m.group(1).split() if m else None
    env = os.environ.copy()
    env["TAU_BA_COMPONENT_FACTORING"] = "1"
    t0 = time.perf_counter()
    try:
        p = subprocess.run([tau, "-q", "-X"], input=text, text=True,
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                           env=env, timeout=120)
        rc = p.returncode
        output = p.stdout
    except subprocess.TimeoutExpired as e:
        rc = 124
        output = (e.stdout or "") + "\nTIMEOUT\n"
    elapsed = time.perf_counter() - t0
    clean = ansi.sub("", output)
    (results_dir / f"{path.stem}.out").write_text(clean)
    actual = answer_re.findall(clean)
    ok = rc == 0 and (expected is None or actual == expected)
    summary.append({"spec": path.name, "expected": expected, "actual": actual,
                    "returncode": rc, "seconds": elapsed, "ok": ok})
    print(f"{path.name}: rc={rc} time={elapsed:.3f}s expected={expected} actual={actual} ok={ok}")
    if not ok:
        print(clean[-5000:])

(results_dir / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
if not all(x["ok"] for x in summary):
    sys.exit(1)
