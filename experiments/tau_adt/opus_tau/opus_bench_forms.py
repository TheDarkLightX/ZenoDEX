#!/usr/bin/env python3
"""Complementary scaling bench: QUERY FORM and ENCODING, not data size.

The lead's bench_scaling.py sweeps bv width, fact-table rows, ADT schema size
and kernel run length. This one holds CONTENT fixed and varies HOW the same
content is asked, which is the axis nomic_07_the_map.tau makes a claim about:
the direct form (`sat always ...` / `valid always (rules -> claim)`) is said
to be "measured correct and fast far beyond real-world rule-set sizes (200+
clauses)" while "the spec-as-value one-off path still has a known scaling
issue there".

Axes here:
  A  direct     sat always (chain && contradiction)        -> unsat
  B  direct     valid always (chain -> long-range claim)   -> valid
  C  { } value  n { chain && contradiction } = 0           -> same question
  D  { } meet   n ({c1} & {c2} & ... & {cN}) = 0           -> law accumulated
                by MEET, which is what the exp4 kernel actually does
All four ask the SAME logical question at the SAME clause count.
"""
import json, os, re, subprocess, sys, time
from pathlib import Path

TAU = sys.argv[1]
OUT = Path(__file__).parent / "bench"; OUT.mkdir(exist_ok=True)
TIMEOUT = float(os.environ.get("BENCH_TIMEOUT", "120"))
HEADER = "set charvar off\nset maxsplits 1\n\n"

def run(name, text, env_extra=None):
    p = OUT / f"{name}.tau"; p.write_text(text)
    env = dict(os.environ); env.update(env_extra or {})
    t0 = time.perf_counter()
    try:
        pr = subprocess.run([TAU, "-q"], stdin=p.open(), capture_output=True,
                            text=True, timeout=TIMEOUT, env=env)
        dt = time.perf_counter() - t0
        clean = re.sub(r"\x1b\[[0-9;?]*[a-zA-Z]", "", pr.stdout)
        ans = [l.split(": ",1)[1].strip() for l in clean.splitlines()
               if l.strip().startswith("%") and ": " in l]
        errs = sum(1 for l in clean.splitlines()
                   if not l.startswith("tau> ") and "(Error)" in l)
        return {"name": name, "s": round(dt,3), "ans": " ".join(ans)[:24], "errs": errs}
    except subprocess.TimeoutExpired:
        return {"name": name, "s": f">{TIMEOUT}", "ans": "TIMEOUT", "errs": 0}

def var(i): return f"o{2*i+7}"
def clauses(n):    # n implication links var(0)->var(1)->...->var(n)
    return [f"({var(i)}[t]=1 -> {var(i+1)}[t]=1)" for i in range(n)]

SIZES = [int(x) for x in os.environ.get("BENCH_SIZES", "17,40,80,120,200,300,400").split(",")]
res = []
for n in SIZES:
    cl = clauses(n)
    chain = " && ".join(cl)
    contra = f"{var(0)}[t]=1 && {var(n)}[t]=0"
    claim  = f"({var(0)}[t]=1 -> {var(n)}[t]=1)"
    # A: direct sat, expect F (unsat: the chain forces var(n)=1)
    res.append(run(f"A_direct_sat_{n}", HEADER + f"sat always ({chain} && {contra}).\n"))
    # B: direct valid entailment, expect T
    res.append(run(f"B_direct_valid_{n}", HEADER + f"valid always (({chain}) -> {claim}).\n"))
    # C: same question through a single { } spec value, expect T (value is 0)
    res.append(run(f"C_value_one_{n}", HEADER + f"n {{ {chain} && {contra} }} = 0\n"))
    # D: law accumulated by MEET of one constant per clause, expect T
    meet = " & ".join("{ %s }" % c for c in cl)
    res.append(run(f"D_value_meet_{n}", HEADER + f"n ({meet} & {{ {contra} }}) = 0\n"))
    print(f"| {res[-4]['name']} | {res[-4]['s']} | {res[-4]['ans']} |", flush=True)
    print(f"| {res[-3]['name']} | {res[-3]['s']} | {res[-3]['ans']} |", flush=True)
    print(f"| {res[-2]['name']} | {res[-2]['s']} | {res[-2]['ans']} |", flush=True)
    print(f"| {res[-1]['name']} | {res[-1]['s']} | {res[-1]['ans']} |", flush=True)
(Path(__file__).parent / "bench_forms.json").write_text(json.dumps(res, indent=1))
