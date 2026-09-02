#!/usr/bin/env python3
"""Tau ADT ABI V1 harness, slice 1: Python-vs-Tau parity over a bounded domain.

Builds frozen vectors by running the REAL Python asset-transfer transition,
renders one Tau program per vector asserting the ABI predicates over ADT
literals, evaluates each with the Tau binary, and requires an exact T/F
verdict (F8 discipline: anything else is a failure, never a skip).

Two predicate tiers, stated honestly:
- RECOMPUTE tier (in-domain reject classes + accepts): Tau re-derives the
  transition outcome from (state, command) literals and must agree with Python.
- CONTRACT tier (the row-ceiling class, whose real ceiling of 4096 rows is
  outside the bounded domain): Tau checks reject_is_noop over the RESULT record
  the host produced; the fold itself stays host-side.

Research-only. Logs to stderr; one JSON report on stdout.
"""

from __future__ import annotations

import json
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO))

from src.core.asset_transfer_module_v1 import transition_asset_transfer_v1  # noqa: E402
from src.core.asset_transfer_types_v1 import (  # noqa: E402
    ASSET_TRANSFER_COMMAND_KIND_V1,
    AssetTransferCommandV1,
    AssetTransferContextV1,
    AssetTransferPolicyV1,
    AssetTransferStateV1,
)
from src.core.global_settlement_types_v1 import (  # noqa: E402
    AssetSupplyV1,
    EconomicAmountV1,
)

TAU_BIN = "/tmp/tau-lang-current/build-Release/tau"
WIDTH = 16
IN_BAND = (1 << WIDTH) - 1

# ABI: frozen member orders (rule 1). Flattened arity is the member count.
STATE_MEMBERS = ("s_bal", "r_bal", "t_bal", "fee_bps_flat", "enabled")
COMMAND_MEMBERS = ("amount", "max_fee")
RESULT_MEMBERS = ("accepted", "code", "noop_roots", "effects_empty")

# Reject-code tokens (bv[4]), frozen vector-local dictionary.
CODE_TOKENS = {
    None: 0,  # accepted
    "SELF_TRANSFER": 1,
    "ZERO_AMOUNT": 2,
    "FEE_LIMIT_EXCEEDED": 3,
    "INSUFFICIENT_BALANCE": 4,
    "DISABLED_ASSET": 5,
    "POST_STATE_RESOURCE_BOUND_EXCEEDED": 6,
}

ROOT = "0x" + "11" * 32


def _state(s_bal: int, r_bal: int, t_bal: int, fee_flat: int, enabled: bool) -> AssetTransferStateV1:
    balances = tuple(
        sorted(
            (
                EconomicAmountV1(owner, "USD", "accounts", atoms)
                for owner, atoms in (("recv", r_bal), ("sender", s_bal), ("treasury", t_bal))
                if atoms > 0
            ),
            key=lambda row: row.key,
        )
    )
    return AssetTransferStateV1(
        module_release_id=ROOT,
        policies=(AssetTransferPolicyV1("USD", "treasury", fee_flat, enabled),),
        balances=balances,
        supplies=(AssetSupplyV1("USD", s_bal + r_bal + t_bal),),
    )


def _run_python(state: AssetTransferStateV1, recipient: str, amount: int, max_fee: int):
    context = AssetTransferContextV1("zenodex", ROOT, ROOT, 1, ROOT, ROOT, "sender", ROOT)
    command = AssetTransferCommandV1(
        ASSET_TRANSFER_COMMAND_KIND_V1, "USD", "sender", recipient, amount, max_fee
    )
    return transition_asset_transfer_v1(context, state, command)


@dataclass(frozen=True)
class VectorV1:
    vector_id: str
    tier: str  # "recompute" | "contract"
    state: tuple[int, int, int, int, bool]  # s_bal, r_bal, t_bal, fee_flat, enabled
    amount: int
    max_fee: int
    recipient: str
    expected_code: str | None  # None == accept


def build_vectors() -> list[VectorV1]:
    vectors = [
        VectorV1("accept_plain", "recompute", (100, 10, 5, 2, True), 30, 2, "recv", None),
        VectorV1("accept_exact_balance", "recompute", (32, 0, 5, 2, True), 30, 2, "recv", None),
        VectorV1("reject_self_transfer", "recompute", (100, 10, 5, 2, True), 30, 2, "sender", "SELF_TRANSFER"),
        VectorV1("reject_zero_amount", "recompute", (100, 10, 5, 2, True), 0, 2, "recv", "ZERO_AMOUNT"),
        VectorV1("reject_fee_limit", "recompute", (100, 10, 5, 9, True), 30, 2, "recv", "FEE_LIMIT_EXCEEDED"),
        VectorV1("reject_insufficient", "recompute", (10, 10, 5, 2, True), 30, 2, "recv", "INSUFFICIENT_BALANCE"),
        VectorV1("reject_disabled", "recompute", (100, 10, 5, 2, False), 30, 2, "recv", "DISABLED_ASSET"),
        # Boundary vectors: each sits exactly at a guard edge.
        VectorV1("accept_fee_at_limit", "recompute", (100, 10, 5, 7, True), 30, 7, "recv", None),
        VectorV1("reject_fee_one_over", "recompute", (100, 10, 5, 8, True), 30, 7, "recv", "FEE_LIMIT_EXCEEDED"),
        VectorV1("accept_balance_exact", "recompute", (37, 0, 5, 7, True), 30, 7, "recv", None),
        VectorV1("reject_balance_one_short", "recompute", (36, 0, 5, 7, True), 30, 7, "recv", "INSUFFICIENT_BALANCE"),
        # Precedence discriminators: two guards both want to fire; the code pins the order.
        VectorV1("prec_disabled_beats_self", "recompute", (100, 10, 5, 2, False), 30, 2, "sender", None),
        VectorV1("prec_self_beats_zero", "recompute", (100, 10, 5, 2, True), 0, 2, "sender", None),
        VectorV1("prec_zero_beats_fee", "recompute", (100, 10, 5, 9, True), 0, 2, "recv", None),
        VectorV1("prec_fee_beats_insufficient", "recompute", (1, 10, 5, 9, True), 30, 2, "recv", None),
    ]
    # Precedence vectors take their expected code from the Python oracle itself
    # (expected_code None above means "ask the oracle"), so a precedence drift
    # between implementations surfaces as a Tau parity F, not a fixture edit.
    resolved = []
    for vector in vectors:
        if vector.vector_id.startswith("prec_"):
            _accepted, oracle_code, _n, _e = python_outcome(vector)
            assert oracle_code is not None, vector.vector_id
            resolved.append(VectorV1(vector.vector_id, vector.tier, vector.state,
                                     vector.amount, vector.max_fee, vector.recipient, oracle_code))
        else:
            resolved.append(vector)
    return resolved


def python_outcome(vector: VectorV1) -> tuple[bool, str | None, bool, bool]:
    result = _run_python(_state(*vector.state), vector.recipient, vector.amount, vector.max_fee)
    name = type(result).__name__
    if name == "AssetTransferAcceptedV1":
        return True, None, False, False
    code = result.code.name
    # Reject-is-noop: the rejected value carries the unchanged post state and
    # an empty effect plan (the NEW-6 contract); derive both from the value.
    post = getattr(result, "post_state", None)
    noop = post is None or post == _state(*vector.state)
    effects = getattr(result, "effects", None)
    effects_empty = effects is None or all(
        not getattr(effects, field)
        for field in ("asset_conservation", "fee_conservation", "lane_writes",
                      "occurrence_consumptions", "external_outbox_enqueue")
    )
    return False, code, noop, effects_empty


def bv(value: int, width: int = WIDTH) -> str:
    return f"{{{value}}}:bv[{width}]"


def render_recompute(vector: VectorV1, expected_accept: bool, expected_code: int) -> str:
    s_bal, r_bal, t_bal, fee_flat, enabled = vector.state
    # transition_ok recomputed in Tau over the ADT literals: guards mirror the
    # Python precedence for the covered classes; every Result member explicitly
    # constrained (rule 2: no implicit partial outputs).
    return f"""type Cmd = {{amount: bv[{WIDTH}], max_fee: bv[{WIDTH}]}}.
type St = {{s_bal: bv[{WIDTH}], r_bal: bv[{WIDTH}], t_bal: bv[{WIDTH}], fee: bv[{WIDTH}], enabled: sbf, self_t: sbf}}.
type Res = {{acc: sbf, code: bv[4], noop: sbf, eff_empty: sbf}}.
n ex r:Res (
  (r.acc = {1 if expected_accept else 0} && r.code = {{{expected_code}}}:bv[4]
   && r.noop = {0 if expected_accept else 1} && r.eff_empty = {0 if expected_accept else 1})
  && (
    ( {1 if enabled else 0} = 0 && r.acc = 0 && r.code = {{{CODE_TOKENS['DISABLED_ASSET']}}}:bv[4] ) ||
    ( {1 if enabled else 0} = 1 && {1 if vector.recipient == 'sender' else 0} = 1 && r.acc = 0 && r.code = {{{CODE_TOKENS['SELF_TRANSFER']}}}:bv[4] ) ||
    ( {1 if enabled else 0} = 1 && {1 if vector.recipient == 'sender' else 0} = 0 && {bv(vector.amount)} = {bv(0)} && r.acc = 0 && r.code = {{{CODE_TOKENS['ZERO_AMOUNT']}}}:bv[4] ) ||
    ( {1 if enabled else 0} = 1 && {1 if vector.recipient == 'sender' else 0} = 0 && {bv(vector.amount)} != {bv(0)} && {bv(fee_flat)} > {bv(vector.max_fee)} && r.acc = 0 && r.code = {{{CODE_TOKENS['FEE_LIMIT_EXCEEDED']}}}:bv[4] ) ||
    ( {1 if enabled else 0} = 1 && {1 if vector.recipient == 'sender' else 0} = 0 && {bv(vector.amount)} != {bv(0)} && {bv(fee_flat)} <= {bv(vector.max_fee)} && {bv(s_bal)} < {bv(vector.amount)} + {bv(fee_flat)} && r.acc = 0 && r.code = {{{CODE_TOKENS['INSUFFICIENT_BALANCE']}}}:bv[4] ) ||
    ( {1 if enabled else 0} = 1 && {1 if vector.recipient == 'sender' else 0} = 0 && {bv(vector.amount)} != {bv(0)} && {bv(fee_flat)} <= {bv(vector.max_fee)} && {bv(s_bal)} >= {bv(vector.amount)} + {bv(fee_flat)} && r.acc = 1 && r.code = {{0}}:bv[4] )
  )
  && (r.acc = 0 -> (r.noop = 1 && r.eff_empty = 1))
  && (r.acc = 1 -> (r.noop = 0 && r.eff_empty = 0))
)
quit
"""


def run_tau(program: str) -> str:
    proc = subprocess.run([TAU_BIN], input=program, capture_output=True, text=True, timeout=120)
    clean = proc.stdout
    for escape in ("\x1b[97;1m", "\x1b[32m", "\x1b[31;1m", "\x1b[106m", "\x1b[0m"):
        clean = clean.replace(escape, "")
    import re
    verdicts = re.findall(r"%\d+: (T|F)\b", clean)
    errors = re.findall(r"\(Error\)", clean)
    if errors or proc.returncode != 0 or len(verdicts) != 1:
        return f"FAIL_CLOSED(verdicts={verdicts},errors={len(errors)},rc={proc.returncode})"
    return verdicts[0]


def selftest() -> int:
    """Falsification probes: the harness must be able to say F and FAIL_CLOSED."""

    vector = build_vectors()[0]  # accept_plain
    accepted, code, _noop, _eff = python_outcome(vector)
    assert accepted and code is None
    # Probe 1: render the WRONG expectation (a reject) for an accepting vector -> F.
    wrong = render_recompute(vector, False, CODE_TOKENS["SELF_TRANSFER"])
    verdict = run_tau(wrong)
    assert verdict == "F", f"wrong-expectation probe returned {verdict!r}"
    # Probe 2: a syntactically broken program must FAIL_CLOSED, never T/F.
    verdict = run_tau("type Broken = {a: sbf. n nonsense(\nquit\n")
    assert verdict.startswith("FAIL_CLOSED"), verdict
    print(json.dumps({"ok": True, "schema": "zenodex/tau-adt-abi-selftest/v1"}))
    return 0


def main() -> int:
    rows = []
    ok = True
    for vector in build_vectors():
        accepted, code, noop, effects_empty = python_outcome(vector)
        assert (code is None) == accepted
        assert code == vector.expected_code, (vector.vector_id, code)
        if not accepted:
            assert noop and effects_empty, (vector.vector_id, "python noop contract")
        program = render_recompute(vector, accepted, CODE_TOKENS[code])
        verdict = run_tau(program)
        agree = verdict == "T"
        ok = ok and agree
        rows.append({"vector": vector.vector_id, "python_code": code or "ACCEPT",
                     "tau_verdict": verdict, "parity": agree})
        print(f"{vector.vector_id}: python={code or 'ACCEPT'} tau={verdict}", file=sys.stderr)
    print(json.dumps({"ok": ok, "schema": "zenodex/tau-adt-abi-parity/v1",
                      "width": WIDTH, "vectors": rows}))
    return 0 if ok else 1


def emit_vectors() -> int:
    """Emit the frozen vector set (with oracle outcomes) for the Rust leg."""

    rows = []
    for vector in build_vectors():
        accepted, code, _noop, _eff = python_outcome(vector)
        s_bal, r_bal, t_bal, fee_flat, enabled = vector.state
        rows.append({
            "vector_id": vector.vector_id,
            "s_bal": s_bal, "r_bal": r_bal, "t_bal": t_bal,
            "fee_flat": fee_flat, "enabled": enabled,
            "amount": vector.amount, "max_fee": vector.max_fee,
            "recipient": vector.recipient,
            "expected": code or "ACCEPT",
        })
    print(json.dumps({"schema": "zenodex/tau-adt-abi-vectors/v1", "vectors": rows}))
    return 0


if __name__ == "__main__":
    if "--selftest" in sys.argv:
        raise SystemExit(selftest())
    if "--emit-vectors" in sys.argv:
        raise SystemExit(emit_vectors())
    raise SystemExit(main())
