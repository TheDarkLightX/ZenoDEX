#!/usr/bin/env python3
"""Verification harness for the ZenoDEX governance pointwise-revision spec suite.

All checks run at Tau's Boolean-function layer (`sat`/`unsat`), NOT the temporal
`always` layer -- a temporal `always` is vacuously satisfied by the empty trace, so
`sat`/`unsat` on it prove nothing. The bf relation is obtained from each temporal spec
by a deterministic transform (drop comment lines, the leading `always`, every `[t]`,
the trailing `.`), so the verified Boolean structure is exactly the runtime spec's.

Check classes:
  1. COMPILE     -- the temporal spec normalizes with 0 errors.
  2. NON-VACUITY -- `sat(body && out=1 && approved && exec_req && timelock_ok)` = T:
                    the gate ADMITS some revision (not vacuously always-reject).
  3. TEETH       -- `unsat(body && out=1 && exec_req && <one guardrail violated>)` = T:
                    each guardrail genuinely rejects (not vacuously always-accept).

The COMPOSITE master couples all five surfaces into one bf that Tau's `sat`/`unsat`
cannot solve as a monolith (a documented envelope limit -- and the reason the design
factors). It is instead verified FACTORED: each `oN` biconditional is extracted and
verified in isolation (tractable, one surface each), plus the `o1` AND-composition bit.

Tau result encoding: `%N: T` (holds) / `%N: F` (does not).
Exit 0 iff every check passes; `--json` writes a machine summary.
"""
from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path

TAU = Path("/home/trevormoc/Downloads/Autonomous Tau DEX/external/tau-lang/build-Release/tau")
SPEC_DIR = Path(__file__).parent
TIMEOUT = 40          # bf sat/unsat checks (per surface / per bit)
COMPILE_TIMEOUT = 150  # full-temporal normalize of a single spec (collateral ~49s)


def bv(v: int) -> str:
    return f"{{ #x{v & 0xFFFF:04X} }}:bv[16]"


def eq(var: str, v: int) -> str:
    return f"({var}:bv[16] = {bv(v)})"


def gt(var: str, v: int) -> str:
    return f"({var}:bv[16] > {bv(v)})"


def lt(var: str, v: int) -> str:
    return f"({var}:bv[16] < {bv(v)})"


def gtv(a: str, b: str) -> str:
    return f"({a}:bv[16] > {b}:bv[16])"


def sbf(var: str, b: int) -> str:
    return f"({var}:sbf = {b}:sbf)"


def strip_comments(text: str) -> str:
    return "\n".join(ln for ln in text.splitlines() if not ln.lstrip().startswith("#"))


def extract_body(spec_path: Path) -> str:
    text = re.sub(r"\s+", " ", strip_comments(spec_path.read_text())).strip()
    assert text.startswith("always"), f"{spec_path.name}: must start with `always`"
    return text[len("always"):].strip().rstrip(".").strip().replace("[t]", "")


def split_top_and(body: str) -> list[str]:
    """Strip the outer parens, split on top-level `&&` (paren-depth aware)."""
    s = body.strip()
    assert s.startswith("(") and s.endswith(")"), "expected a parenthesized conjunction"
    s = s[1:-1].strip()
    pieces, depth, cur, i = [], 0, "", 0
    while i < len(s):
        ch = s[i]
        if ch == "(":
            depth += 1; cur += ch
        elif ch == ")":
            depth -= 1; cur += ch
        elif depth == 0 and s[i:i + 2] == "&&":
            pieces.append(cur.strip()); cur = ""; i += 2; continue
        else:
            cur += ch
        i += 1
    if cur.strip():
        pieces.append(cur.strip())
    return pieces


def run_tau(query: str) -> str:
    try:
        proc = subprocess.run(
            [str(TAU), "--charvar", "false"],
            input=f"{query}\nq\n", capture_output=True, text=True, timeout=TIMEOUT,
        )
    except subprocess.TimeoutExpired:
        return "TIMEOUT"
    raw = re.sub(r"\x1b\[[0-9;]*m", "", proc.stdout + proc.stderr)
    if re.search(r"\bError\b|\berror:", raw):
        return "ERR"
    m = re.findall(r"%\d+:\s*([TF])\b", raw)
    return m[-1] if m else "?"


def _normalizes(text: str, timeout: int) -> bool:
    """True iff Tau normalizes `text` with no error and produces a `<->` form."""
    try:
        proc = subprocess.run(
            [str(TAU), "--charvar", "false"],
            input=f"{text}\nq\n", capture_output=True, text=True, timeout=timeout,
        )
    except subprocess.TimeoutExpired:
        return False
    raw = re.sub(r"\x1b\[[0-9;]*m", "", proc.stdout + proc.stderr)
    return not re.search(r"\bError\b|\berror:", raw) and "<->" in raw


def compile_ok(spec_path: Path) -> bool:
    """Full-temporal normalize of a single spec (the runtime contract)."""
    return _normalizes(strip_comments(spec_path.read_text()), COMPILE_TIMEOUT)


def check(formula: str, cmd: str, clauses: list[str]) -> str:
    return run_tau(f"{cmd} ({formula}) && " + " && ".join(clauses))


# Shared timelock-ok inputs: proposal=0, current=24 (gap 24 == MIN_DELAY).
GATE_OK = [sbf("i1", 1), sbf("i2", 1), eq("i3", 0x0000), eq("i4", 0x0018)]
EXEC = sbf("i2", 1)
TL_BAD = [sbf("i1", 1), eq("i3", 0x0064), eq("i4", 0x006E)]  # gap 10 < 24


# (spec file, output bit, non-vacuity clauses, [(teeth name, violation clauses)])
PER_SURFACE = {
    "gov_fee_revision_v1.tau": ("o1", GATE_OK, [
        ("fee_above_cap_1000", [gt("i6", 0x03E8)]),
        ("fee_step_over_50", [eq("i5", 0x0000), eq("i6", 0x00C8)]),
        ("not_approved", [sbf("i1", 0)]),
        ("timelock_not_met", TL_BAD),
    ]),
    # router SUM-BUDGET gate: next shares i5-i8
    "gov_router_split_revision_v1.tau": ("o1", GATE_OK, [
        ("sum_below_10000", [eq("i5", 0), eq("i6", 0), eq("i7", 0), eq("i8", 0)]),
        ("sum_above_10000", [eq("i5", 0x2710), eq("i6", 0x2710), eq("i7", 0), eq("i8", 0)]),
        ("buyburn_over_100pct", [gt("i5", 0x2710)]),
        ("stakers_over_100pct", [gt("i6", 0x2710)]),
        ("reserve_over_100pct", [gt("i7", 0x2710)]),
        ("hosts_over_100pct", [gt("i8", 0x2710)]),
        ("not_approved", [sbf("i1", 0)]),
        ("timelock_not_met", TL_BAD),
    ]),
    # NOTE: the router PER-SHARE DRIFT gate is NOT a standalone spec — each share's step is the
    # universal gov_action_bound gate (lo=0, hi=10000, step=500), verified above; the COMBINED
    # 4-step is the master `o6` bit, verified below. (A standalone 4-step temporal spec normalizes
    # in ~180s on the current build — too heavy/flaky to gate on; the factored form is tractable.)
    "gov_funding_rate_revision_v1.tau": ("o1", GATE_OK, [
        ("funding_above_cap_200", [gt("i6", 0x00C8)]),
        ("funding_step_over_25", [eq("i5", 0x0000), eq("i6", 0x0064)]),  # 0 -> 100 drift 100 > 25
        ("not_approved", [sbf("i1", 0)]),
        ("timelock_not_met", TL_BAD),
    ]),
    "gov_collateral_ratio_revision_v1.tau": ("o1", GATE_OK, [
        ("mcr_below_floor", [lt("i6", 0x2710)]),
        ("ccr_above_ceiling", [gt("i8", 0x7530)]),
        ("mcr_exceeds_ccr", [gtv("i6", "i8")]),
        ("mcr_step_over_1000", [eq("i5", 0x2AF8), eq("i6", 0x4E20)]),   # 11000 -> 20000 drift 9000
        ("ccr_step_over_1000", [eq("i7", 0x3A98), eq("i8", 0x61A8)]),   # 15000 -> 25000 drift 10000
        ("not_approved", [sbf("i1", 0)]),
        ("timelock_not_met", TL_BAD),
    ]),
    "gov_whale_defense_revision_v1.tau": ("o1", GATE_OK, [
        ("staker_bps_above_7000", [gt("i6", 0x1B58)]),
        ("step_over_500", [eq("i5", 0x0000), eq("i6", 0x07D0)]),
        ("not_approved", [sbf("i1", 0)]),
        ("timelock_not_met", TL_BAD),
    ]),
    "gov_action_bound_v1.tau": ("o1",
        [sbf("i1", 1), sbf("i2", 1), eq("i3", 0), eq("i4", 0x0018), eq("i5", 0x0018),
         eq("i8", 0x0000), eq("i9", 0x03E8), eq("i10", 0x0032)], [
        ("next_above_max", [eq("i8", 0), eq("i9", 0x03E8), gt("i7", 0x03E8)]),
        ("next_below_min", [eq("i8", 0x0064), lt("i7", 0x0064)]),
        ("step_exceeded", [eq("i5", 0x0018), eq("i6", 0), eq("i7", 0x00C8),
                           eq("i8", 0), eq("i9", 0x03E8), eq("i10", 0x0032)]),
        ("not_approved", [sbf("i1", 0)]),
        ("timelock_not_met", TL_BAD + [eq("i5", 0x0018)]),  # i5 is min_delay for this gate
    ]),
}

# Master bit -> (non-vacuity clauses, [(teeth name, violation clauses)]). Verified per bit.
# Master input layout: fee i5/i6; router next i7-i10, curr i11-i14; collateral i15-i18;
# whale i19/i20. Router is two bits (o3 sum, o6 step). EVERY guardrail of every bit gets a
# teeth (Codex MED). NOTE: master bit IDs are verified against the composition (o2,o3,o6,o4,o5).
MASTER_BITS = {
    "o2": ([], [("fee_cap", [gt("i6", 0x03E8)]),
                ("fee_step", [eq("i5", 0), eq("i6", 0x00C8)])]),
    "o3": ([], [("buyburn_cap", [gt("i7", 0x2710)]),
                ("stakers_cap", [gt("i8", 0x2710)]),
                ("reserve_cap", [gt("i9", 0x2710)]),
                ("hosts_cap", [gt("i10", 0x2710)]),
                ("sum", [eq("i7", 0), eq("i8", 0), eq("i9", 0), eq("i10", 0)])]),
    "o6": ([], [("buyburn_step", [eq("i11", 0x0000), eq("i7", 0x07D0)]),  # curr 0 -> next 2000
                ("stakers_step", [eq("i12", 0x0000), eq("i8", 0x07D0)]),
                ("reserve_step", [eq("i13", 0x0000), eq("i9", 0x07D0)]),
                ("hosts_step", [eq("i14", 0x0000), eq("i10", 0x07D0)])]),
    "o4": ([], [("mcr_floor", [lt("i16", 0x2710)]),
                ("ccr_ceiling", [gt("i18", 0x7530)]),
                ("order", [gtv("i16", "i18")]),
                ("mcr_step", [eq("i15", 0x2AF8), eq("i16", 0x4E20)]),
                ("ccr_step", [eq("i17", 0x3A98), eq("i18", 0x61A8)])]),
    "o5": ([], [("whale_ceiling", [gt("i20", 0x1B58)]),
                ("whale_step", [eq("i19", 0), eq("i20", 0x07D0)])]),
}


def verify_per_surface(name: str, out: str, nonvac: list[str], teeth: list) -> dict:
    spec_path = SPEC_DIR / name
    body = extract_body(spec_path)
    res = {"compile": compile_ok(spec_path),
           "non_vacuity": check(body, "sat", [sbf(out, 1)] + nonvac) == "T",
           "teeth": {}}
    for tname, clauses in teeth:
        res["teeth"][tname] = check(body, "unsat", [sbf(out, 1), EXEC] + clauses) == "T"
    res["pass"] = res["compile"] and res["non_vacuity"] and all(res["teeth"].values())
    return res


def verify_master() -> dict:
    spec_path = SPEC_DIR / "gov_revision_master_v1.tau"
    body = extract_body(spec_path)
    pieces = {m.group(1): p for p in split_top_and(body)
              if (m := re.search(r"\b(o\d):sbf = 1:sbf <->", p))}
    # The master's MONOLITH normalize is intractable (the documented coupling/envelope limit).
    # Compile is established FACTORED: each of the 6 biconditional pieces normalizes on its own,
    # and the suite extracted exactly the expected o1..o6 components (o3 router-sum, o6 router-step).
    res = {
        "compile_monolith": "intractable_by_design",
        "compile_pieces": (len(pieces) == 6
                           and all(_normalizes(p, TIMEOUT) for p in pieces.values())),
        "bits": {}, "composition": {},
    }

    # Each guardrail bit (o2, o3, o6, o4, o5): non-vacuous + each teeth, verified in isolation.
    for bit, (_, teeth) in MASTER_BITS.items():
        piece = pieces.get(bit)
        if not piece:
            res["bits"][bit] = {"pass": False, "error": "bit not found"}
            continue
        b = {"non_vacuity": check(piece, "sat", [sbf(bit, 1)]) == "T", "teeth": {}}
        for tname, clauses in teeth:
            b["teeth"][tname] = check(piece, "unsat", [sbf(bit, 1)] + clauses) == "T"
        b["pass"] = b["non_vacuity"] and all(b["teeth"].values())
        res["bits"][bit] = b

    # Composition bit o1 = (exec=0 OR (approved AND timelock AND o2 AND o3 AND o6 AND o4 AND o5)).
    o1 = pieces.get("o1", "")
    res["composition"] = {
        # any surface bit 0 (with exec requested + gate ok) => o1 cannot be 1
        "requires_all_bits": all(
            check(o1, "unsat", [sbf("o1", 1), EXEC, sbf("i1", 1), eq("i3", 0), eq("i4", 0x0018),
                                sbf(z, 0)]) == "T"
            for z in ("o2", "o3", "o6", "o4", "o5")),
        "requires_approval": check(o1, "unsat", [sbf("o1", 1), EXEC, sbf("i1", 0)]) == "T",
        "requires_timelock": check(o1, "unsat", [sbf("o1", 1), EXEC] + TL_BAD) == "T",
        # all bits set + gate ok => o1 admits
        "admits_all_good": check(o1, "sat", [sbf("o1", 1), sbf("i1", 1), EXEC, eq("i3", 0),
                                             eq("i4", 0x0018), sbf("o2", 1), sbf("o3", 1),
                                             sbf("o6", 1), sbf("o4", 1), sbf("o5", 1)]) == "T",
    }
    bits_ok = all(b.get("pass") for b in res["bits"].values())
    res["pass"] = res["compile_pieces"] and bits_ok and all(res["composition"].values())
    return res


def main() -> int:
    as_json = "--json" in sys.argv
    if not TAU.exists():
        print(f"tau binary not found at {TAU}", file=sys.stderr)
        return 2

    summary: dict = {"per_surface": {}, "master": {}, "all_pass": True}
    for name, (out, nonvac, teeth) in PER_SURFACE.items():
        if not as_json:
            print(f"[verify] {name} ...", flush=True)
        r = verify_per_surface(name, out, nonvac, teeth)
        summary["per_surface"][name] = r
        summary["all_pass"] = summary["all_pass"] and r["pass"]
        if not as_json:
            t = sum(r["teeth"].values())
            print(f"   compile={'OK' if r['compile'] else 'FAIL'} "
                  f"sat={'OK' if r['non_vacuity'] else 'FAIL'} "
                  f"teeth={t}/{len(r['teeth'])} -> {'PASS' if r['pass'] else 'FAIL'}", flush=True)

    if not as_json:
        print("[verify] gov_revision_master_v1.tau (factored, bit-by-bit) ...", flush=True)
    m = verify_master()
    summary["master"] = m
    summary["all_pass"] = summary["all_pass"] and m["pass"]
    if not as_json:
        bn = sum(1 for b in m["bits"].values() if b.get("pass"))
        cn = sum(1 for v in m["composition"].values() if v)
        print(f"   compile(pieces)={'OK' if m['compile_pieces'] else 'FAIL'} "
              f"(monolith={m['compile_monolith']}) bits={bn}/{len(m['bits'])} "
              f"composition={cn}/{len(m['composition'])} -> {'PASS' if m['pass'] else 'FAIL'}", flush=True)

    if as_json:
        print(json.dumps(summary, indent=2))
    else:
        print("\n" + ("ALL PASS" if summary["all_pass"] else "FAILURES PRESENT"))
    return 0 if summary["all_pass"] else 1


if __name__ == "__main__":
    sys.exit(main())
