#!/usr/bin/env python3
"""Bench 4: does the { }-entailment cliff appear INSIDE the running kernel?

The lead's axis 4 sweeps admission-kernel RUN LENGTH. This sweeps the other
dimension of the same machine: POLICY SIZE. My repaired kernel's policy test
is `i1[t] & o0s[t-1]' != 0` - an entailment against a { } constant, i.e.
exactly the E_admit_value form that fell off a cliff between 32 and 64
clauses as a one-off query. Two steps, fixed; only the policy grows.
"""
import json, os, re, subprocess, sys, time
from pathlib import Path
TAU = sys.argv[1]
OUT = Path(__file__).parent / "bench"; OUT.mkdir(exist_ok=True)
TIMEOUT = float(os.environ.get("BENCH_TIMEOUT", "200"))

KERNEL = ("run ( (o0s[0]:tau = {{ {pol} }}) && (o0sp[0]:tau = 0) && "
 "( (((i1[t]:tau & i2[t]:tau') != 0) || ((i2[t]:tau') = 0)) ? "
 "((o0s[t]:tau = o0s[t-1]:tau) && (o0sp[t]:tau = o0sp[t-1]:tau) && (o0res[t]:bv[8] = {{ #x06 }}:bv[8])) : "
 "( ((o0sp[t-1]:tau & i2[t]:tau) != 0) ? "
 "((o0s[t]:tau = o0s[t-1]:tau) && (o0sp[t]:tau = o0sp[t-1]:tau) && (o0res[t]:bv[8] = {{ #x07 }}:bv[8])) : "
 "( ((i1[t]:tau & o0s[t-1]:tau') != 0) ? "
 "((o0s[t]:tau = o0s[t-1]:tau) && (o0sp[t]:tau = o0sp[t-1]:tau) && (o0res[t]:bv[8] = {{ #x08 }}:bv[8])) : "
 "((o0s[t]:tau = o0s[t-1]:tau) && (o0sp[t]:tau = (o0sp[t-1]:tau | i2[t]:tau)) && (o0res[t]:bv[8] = {{ #x09 }}:bv[8])) ) ) ) )\n")

res = []
for n in (2, 4, 8, 16, 32):
    pol = " && ".join(f"(oact{i}[t]=1 -> oauth{i}[t]=1)" for i in range(n))
    spend = " && ".join(f"oauth{i}[t]=1" for i in range(n))
    text = ("set charvar off\n" + KERNEL.format(pol=pol)
            + f"onul[t]:bv[8] = {{ #x04 }}:bv[8] && {spend}\n"
            + "onul[t]:bv[8] = { #x04 }:bv[8]\n"
            + f"onul[t]:bv[8] = {{ #x04 }}:bv[8] && {spend}\n"
            + "onul[t]:bv[8] = { #x04 }:bv[8]\n")
    p = OUT / f"K_policy{n}.tau"; p.write_text(text)
    t0 = time.perf_counter()
    try:
        pr = subprocess.run([TAU, "-q"], stdin=p.open(), capture_output=True,
                            text=True, timeout=TIMEOUT, env=dict(os.environ))
        dt = time.perf_counter() - t0
        clean = re.sub(r"\x1b\[[0-9;?]*[a-zA-Z]", "", pr.stdout)
        codes = [m for l in clean.splitlines() if not l.startswith("tau> ")
                 for m in re.findall(r"o0res\[\d+\] *:= *\{? *(\d+)", l)]
        r = {"name": f"K_policy{n}", "s": round(dt,3), "codes": ",".join(codes)}
    except subprocess.TimeoutExpired:
        r = {"name": f"K_policy{n}", "s": f">{TIMEOUT}", "codes": "TIMEOUT"}
    res.append(r); print(f"| {r['name']} | {r['s']} | {r['codes']} |", flush=True)
Path(__file__).parent.joinpath("bench_kernel_policy.json").write_text(json.dumps(res, indent=1))
