#!/usr/bin/env python3
"""Bench 2: the per-trade admission question in both encodings, the new table
kinds at 2x/4x/8x, and query-form cost (n vs sat vs valid vs solve).

Complementary to bench_scaling.py (data size) and opus_bench_forms.py (rule-set
size). Here the question is the one a DEX actually runs per trade.
"""
import json, os, re, subprocess, sys, time
from pathlib import Path

TAU = sys.argv[1]
OUT = Path(__file__).parent / "bench"; OUT.mkdir(exist_ok=True)
TIMEOUT = float(os.environ.get("BENCH_TIMEOUT", "180"))
HEADER = "set charvar off\nset maxsplits 1\n\n"

def run(name, text):
    p = OUT / f"{name}.tau"; p.write_text(text)
    t0 = time.perf_counter()
    try:
        pr = subprocess.run([TAU, "-q"], stdin=p.open(), capture_output=True,
                            text=True, timeout=TIMEOUT, env=dict(os.environ))
        dt = time.perf_counter() - t0
        clean = re.sub(r"\x1b\[[0-9;?]*[a-zA-Z]", "", pr.stdout)
        ans = [l.split(": ",1)[1].strip() for l in clean.splitlines()
               if l.strip().startswith("%") and ": " in l]
        sol = sum(1 for l in clean.splitlines() if ":=" in l and not l.startswith("tau> "))
        errs = sum(1 for l in clean.splitlines()
                   if not l.startswith("tau> ") and "(Error)" in l)
        return {"name": name, "s": round(dt,3), "ans": (" ".join(ans)[:20] or f"{sol} bindings"), "errs": errs}
    except subprocess.TimeoutExpired:
        return {"name": name, "s": f">{TIMEOUT}", "ans": "TIMEOUT", "errs": 0}

def hx(v, w=8): return "{ #x%0*x }:bv[%d]" % (max(1, w//4), v, w)
res = []
def add(r):
    res.append(r); print(f"| {r['name']} | {r['s']} | {r['ans']} | {r['errs']} |", flush=True)

# ===== E: THE PER-TRADE ADMISSION QUESTION, two encodings ====================
# policy P = N independent authorization clauses; spend x satisfies them all.
# (i) { } entailment  n (x & P') = 0      (ii) direct  valid always (x -> P).
for n in (4, 8, 16, 32, 64, 128):
    pol = " && ".join(f"(oact{i}[t]=1 -> oauth{i}[t]=1)" for i in range(n))
    spend = " && ".join(f"oauth{i}[t]=1" for i in range(n))
    add(run(f"E_admit_value_{n}",  HEADER + f"n ({{ {spend} }} & {{ {pol} }}') = 0\n"))
    add(run(f"E_admit_direct_{n}", HEADER + f"valid always (({spend}) -> ({pol})).\n"))

# ===== F1: CROSSING TABLE at 2x/4x/8x =======================================
for n in (2, 4, 8, 16):
    bids = " | ".join("{ obpx[t]:bv[8] = %s && obq[t]:bv[8] = %s }" % (hx(2*i+1), hx(10)) for i in range(n))
    asks = " | ".join("{ oapx[t]:bv[8] = %s && oaq[t]:bv[8] = %s }" % (hx(2*i+2), hx(10)) for i in range(n))
    add(run(f"F1_crossing_{n}x{n}", HEADER + f"n (({bids}) & ({asks}) & {{ obpx[t]:bv[8] >= oapx[t]:bv[8] }}) != 0\n"))

# ===== F2: KEY-PROJECTED REGISTRY at 2x/4x/8x ===============================
for n in (2, 4, 8, 16, 32, 64):
    reg = " | ".join("{ onul[t]:bv[16] = %s }" % hx(i+1, 16) for i in range(n))
    # membership of a registered key, and the fresh-key negative
    add(run(f"F2_registry_{n}", HEADER +
            f"n (({{ onul[t]:bv[16] = {hx(n,16)} && oauth[t]=1 }}) & ({reg})) != 0\n"
            f"n (({{ onul[t]:bv[16] = {hx(5000,16)} }}) & ({reg})) = 0\n"))

# ===== F3: GUARDED ESCROW, widening the account table =======================
for n in (2, 3, 4, 6, 8):
    cells = ", ".join(f"a{i}: bv[8]" for i in range(n))
    carry = " && ".join(f"f.a{i} = e.a{i}" for i in range(2, n))
    carry = (" && " + carry) if carry else ""
    tot_e = " + ".join(f"e.a{i}" for i in range(n))
    tot_f = " + ".join(f"f.a{i}" for i in range(n))
    body = (f"type Esc = {{{cells}}}. n all e:Esc all f:Esc all d:bv[8] "
            f"((d <= e.a0 && e.a1 <= {hx(255)} - d && f.a0 = e.a0 - d && f.a1 = e.a1 + d{carry}) "
            f"-> (f.a0 <= e.a0 && f.a1 >= e.a1 && {tot_f} = {tot_e}))\n")
    add(run(f"F3_escrow_cells{n}", HEADER + body))

# ===== G: QUERY FORM at fixed content (8-row table) =========================
rows = " | ".join("{ oid[t]:bv[8] = %s && oqty[t]:bv[8] = %s }" % (hx(i+1), hx(10*(i+1))) for i in range(8))
probe = "{ oid[t]:bv[8] = %s && oqty[t]:bv[8] = %s }" % (hx(8), hx(80))
add(run("G_form_n_membership",  HEADER + f"n (({probe}) & ({rows})') = 0\n"))
add(run("G_form_n_overlap",     HEADER + f"n (({probe}) & ({rows})) != 0\n"))
add(run("G_form_solve_witness", HEADER + f"solve t:bv[8] = t && (({probe}) & ({rows})) != 0 && t = {hx(8)}\n"))
add(run("G_form_sat_direct",    HEADER + f"sat always (oid[t]:bv[8] = {hx(8)} && oqty[t]:bv[8] = {hx(80)}).\n"))

(Path(__file__).parent / "bench_kinds.json").write_text(json.dumps(res, indent=1))
