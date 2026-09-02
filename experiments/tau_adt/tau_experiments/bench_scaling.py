#!/usr/bin/env python3
"""Empirical scaling walls for Tau-table constructions (ZenoDEX partition study).

Emits generated .tau files, times each under a hard timeout, prints a markdown
table. Axes: bv width (conservation theorem), fact-table rows (membership +
audit diff), ADT fixed-schema rows (proven total), admission-kernel steps
(accumulated-state growth), and TAU_BA_COMPONENT_FACTORING on/off for the
heaviest case.
"""
import json, os, subprocess, sys, time
from pathlib import Path

TAU = sys.argv[1]
OUT = Path(__file__).parent / "bench"
OUT.mkdir(exist_ok=True)
TIMEOUT = float(os.environ.get("BENCH_TIMEOUT", "120"))
HEADER = "set charvar off\nset maxsplits 1\n\n"

def run(name: str, text: str, env_extra=None) -> dict:
    path = OUT / f"{name}.tau"
    path.write_text(text)
    env = dict(os.environ)
    if env_extra:
        env.update(env_extra)
    t0 = time.perf_counter()
    try:
        proc = subprocess.run([TAU, "-q"], stdin=path.open(), capture_output=True,
                              text=True, timeout=TIMEOUT, env=env)
        dt = time.perf_counter() - t0
        import re as _re
        clean = _re.sub(r"\x1b\[[0-9;?]*[a-zA-Z]", "", proc.stdout)
        answers = [line.split(": ", 1)[1] for line in clean.splitlines()
                   if line.strip().startswith("%") and ": " in line]
        errors = sum(1 for line in (proc.stdout + proc.stderr).splitlines() if "rror" in line)
        return {"name": name, "s": round(dt, 3), "answers": " ".join(a.strip() for a in answers)[:40], "errs": errors}
    except subprocess.TimeoutExpired:
        return {"name": name, "s": f">{TIMEOUT}", "answers": "TIMEOUT", "errs": 0}

def hexlit(v: int, w: int) -> str:
    return "{ #x%0*x }:bv[%d]" % (max(1, w // 4), v, w)

results = []

# --- axis 1: bv width, conservation theorem + refuted lossy control ---------
for w in (8, 16, 32, 64):
    ten, five, three, two = hexlit(10, w), hexlit(5, w), hexlit(3, w), hexlit(2, w)
    body = (f"type Bal = {{alice: bv[{w}], bob: bv[{w}]}}. "
            f"n all b:Bal all c:Bal ((b.alice = {ten} && b.bob = {five} && "
            f"c.alice = b.alice - {three} && c.bob = b.bob + {three}) -> "
            f"c.alice + c.bob = b.alice + b.bob)\n"
            f"type Bal = {{alice: bv[{w}], bob: bv[{w}]}}. "
            f"n ex b:Bal ex c:Bal (b.alice = {ten} && b.bob = {five} && "
            f"c.alice = b.alice - {three} && c.bob = b.bob + {two} && "
            f"c.alice + c.bob = b.alice + b.bob)\n")
    results.append(run(f"conserve_bv{w}", HEADER + body))

# --- axis 2: fact-table rows, membership + missing-key negative -------------
for n in (2, 4, 8, 16, 32, 64):
    rows = " | ".join("{ oid[t]:bv[16] = %s && oqty[t]:bv[16] = %s }" % (hexlit(i + 1, 16), hexlit(10 * (i + 1), 16)) for i in range(n))
    member = "{ oid[t]:bv[16] = %s && oqty[t]:bv[16] = %s }" % (hexlit(n, 16), hexlit(10 * n, 16))
    absent = "{ oid[t]:bv[16] = %s }" % hexlit(2000, 16)
    body = (f"n (({member}) & ({rows})') = 0\n"
            f"n (({absent}) & ({rows})) = 0\n")
    results.append(run(f"table_rows{n}", HEADER + body))

# --- axis 3: ADT fixed-schema proven total ----------------------------------
for n in (2, 4, 8, 12):
    members = ", ".join(f"r{i}: Row" for i in range(n))
    fixes = " && ".join(f"t.r{i}.qty = {hexlit(10, 16)}" for i in range(n))
    total = " + ".join(f"t.r{i}.qty" for i in range(n))
    body = (f"type Row = {{id: bv[16], qty: bv[16]}}. type Tab = {{{members}}}. "
            f"n all t:Tab (({fixes}) -> {total} = {hexlit(10 * n, 16)})\n")
    results.append(run(f"adt_total_rows{n}", HEADER + body))

# --- axis 4: admission-kernel run length (state accumulates per step) -------
KERNEL = ("run ( (o0s[0]:tau = { oact[t]=1 -> oauth[t]=1 }) && (o0sp[0]:tau = 0) && "
          "( ((o0sp[t-1]:tau & i1[t]:tau) != 0) ? ((o0s[t]:tau = o0s[t-1]:tau) && (o0sp[t]:tau = o0sp[t-1]:tau) && (o0res[t]:bv[8] = { #x07 }:bv[8])) : "
          "( ((o0s[t-1]:tau & i1[t]:tau) != 0) ? ((o0s[t]:tau = o0s[t-1]:tau) && (o0sp[t]:tau = (o0sp[t-1]:tau | i1[t]:tau)) && (o0res[t]:bv[8] = { #x09 }:bv[8])) : "
          "((o0s[t]:tau = o0s[t-1]:tau) && (o0sp[t]:tau = o0sp[t-1]:tau) && (o0res[t]:bv[8] = { #x08 }:bv[8])) ) ) )\n")
for steps in (3, 6, 10, 15):
    inputs = "".join("onul[t]:bv[16] = %s && oauth[t]=1\n" % hexlit(100 + i, 16) for i in range(steps))
    results.append(run(f"kernel_steps{steps}", "set charvar off\n\n" + KERNEL + inputs))

# --- axis 5: component factoring on the heaviest surviving case -------------
heavy = None
for r in reversed(results):
    if r["name"].startswith("kernel_steps") and r["answers"] != "TIMEOUT":
        heavy = r["name"]; break
if heavy:
    steps = int(heavy.replace("kernel_steps", ""))
    inputs = "".join("onul[t]:bv[16] = %s && oauth[t]=1\n" % hexlit(100 + i, 16) for i in range(steps))
    results.append(run(f"kernel_steps{steps}_factored", "set charvar off\n\n" + KERNEL + inputs,
                       env_extra={"TAU_BA_COMPONENT_FACTORING": "1"}))

print("| case | seconds | answers | err-lines |")
print("|---|---|---|---|")
for r in results:
    print(f"| {r['name']} | {r['s']} | {r['answers']} | {r['errs']} |")
(Path(__file__).parent / "bench_results.json").write_text(json.dumps(results, indent=1))
