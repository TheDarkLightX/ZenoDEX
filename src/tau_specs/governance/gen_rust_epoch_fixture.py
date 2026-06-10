#!/usr/bin/env python3
"""Generate the cross-language EPOCH-MACHINE scenario fixture for the Rust port.

Single source of truth: gov_epoch.py ITSELF — this script REPLAYS deterministic
scenario scripts through the Python machine and records, after every transition,
the full observable outcome (receipt code/surface/digests/pin + params + per-
surface trajectory + charter + frozen + pending). The Rust `epoch` module must
reproduce every recorded field transition-by-transition
(rust-runtime/crates/zenodex-governance-gate/tests/epoch_parity.rs);
test_gov_parity.py byte-pins the committed JSON so it cannot drift from this
generator.

Coverage is asserted: the scenarios must exercise ALL receipt codes and all
three surface-gate reject labels (scalar / "router" / "collateral"). Python's
raise-paths (hostile/malformed objects) are NOT in scope — they are
unrepresentable in the typed Rust core; `EpochError` mirrors the two remaining
value-domain raises and is unit-tested on the Rust side.

Regenerate with:  python3 src/tau_specs/governance/gen_rust_epoch_fixture.py
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

_GOV = Path(__file__).resolve().parent
sys.path.insert(0, str(_GOV))

import gov_epoch as ge  # noqa: E402

FIXTURE = (_GOV.parents[2] / "tests" / "tau_specs" / "governance"
           / "fixtures" / "gov_epoch_scenarios.json")

GENESIS = {
    "fee_bps": 500, "funding_cap_bps": 100, "redeem_staker_bps": 6000,
    "buyburn_bps": 6000, "stakers_bps": 0, "reserve_bps": 2000, "hosts_bps": 2000,
    "mcr_bps": 11000, "ccr_bps": 15000,
}
PIN = "ab" * 32

# Scenario scripts: (op, args) tuples. "genesis" resets the machine.
SCENARIOS: list[tuple[str, list[tuple[str, dict[str, object]]]]] = [
    ("lifecycle_and_walk", [
        ("genesis", {"params": GENESIS, "epoch": 0}),
        ("propose", {"deltas": {"fee_bps": 50}, "now": 0}),       # charter_invalid
        ("revoke", {"now": 0}),                                    # no_charter
        ("renew", {"now": 0, "ttl": 4096, "pin": PIN}),
        ("propose", {"deltas": {}, "now": 0}),                     # empty_action
        ("propose", {"deltas": {"fee_bps": 50}, "now": 0}),
        ("propose", {"deltas": {"fee_bps": 10}, "now": 1}),        # pending_exists
        ("apply", {"now": 23}),                                    # timelock (kept)
        ("apply", {"now": 48}),                                    # applied 550
        ("propose", {"deltas": {"fee_bps": 10}, "now": 48}),
        ("apply", {"now": 72}),                                    # cooldown (cleared)
        ("propose", {"deltas": {"fee_bps": 50}, "now": 96}),
        ("apply", {"now": 144}),                                   # applied 600
        ("propose", {"deltas": {"fee_bps": 50}, "now": 144}),
        ("apply", {"now": 192}),                                   # applied 650
        ("propose", {"deltas": {"fee_bps": 50}, "now": 192}),
        ("apply", {"now": 240}),                                   # drift_budget
        ("propose", {"deltas": {"fee_bps": 50}, "now": 700}),
        ("apply", {"now": 748}),                                   # applied 700 (window rolled)
        ("propose", {"deltas": {"funding_cap_bps": 25}, "now": 748}),
        ("veto", {"now": 749}),                                    # vetoed
        ("apply", {"now": 800}),                                   # no_pending
        ("propose", {"deltas": {"funding_cap_bps": 25}, "now": 800}),
        ("freeze", {"now": 801}),
        ("propose", {"deltas": {"redeem_staker_bps": 100}, "now": 801}),  # frozen
        ("apply", {"now": 830}),                                   # frozen (cleared)
        ("unfreeze", {"now": 831}),
        ("propose", {"deltas": {"funding_cap_bps": 25}, "now": 831}),
        ("apply", {"now": 879}),                                   # applied 125
    ]),
    ("gates_and_budgets", [
        ("genesis", {"params": GENESIS, "epoch": 0}),
        ("renew", {"now": 0, "ttl": 4096, "pin": PIN}),
        ("propose", {"deltas": {"fee_bps": 60}, "now": 0}),
        ("apply", {"now": 48}),                                    # surface_gate fee_bps
        ("propose", {"deltas": {"buyburn_bps": -500, "stakers_bps": 500,
                                "reserve_bps": -500, "hosts_bps": 500}, "now": 48}),
        ("apply", {"now": 96}),                                    # applied (aggregate 2000 boundary)
        ("propose", {"deltas": {"buyburn_bps": 500}, "now": 96}),
        ("apply", {"now": 144}),                                   # surface_gate router (sum breaks)
        ("propose", {"deltas": {"mcr_bps": 1000, "ccr_bps": 1000, "fee_bps": 50}, "now": 144}),
        ("apply", {"now": 192}),                                   # epoch_budget (2050)
        ("propose", {"deltas": {"mcr_bps": -2000}, "now": 192}),
        ("apply", {"now": 240}),                                   # surface_gate collateral (step)
    ]),
    ("charter_dead_man", [
        ("genesis", {"params": GENESIS, "epoch": 0}),
        ("renew", {"now": 0, "ttl": 100, "pin": PIN}),
        ("propose", {"deltas": {"fee_bps": 50}, "now": 70}),
        ("apply", {"now": 100}),                                   # charter expired (cleared)
        ("propose", {"deltas": {"fee_bps": 10}, "now": 101}),      # charter_invalid
        ("renew", {"now": 101, "ttl": 100, "pin": PIN}),
        ("revoke", {"now": 102}),                                  # revoked
        ("revoke", {"now": 103}),                                  # idempotent revoke
        ("propose", {"deltas": {"fee_bps": 10}, "now": 103}),      # charter_invalid
        ("freeze", {"now": 104}),
        ("veto", {"now": 105}),                                    # no_pending (veto never gated)
        ("unfreeze", {"now": 106}),
    ]),
]


def _observe(state: ge.GovEpochState) -> dict[str, object]:
    traj = {k: {"last_revision_epoch": t.last_revision_epoch,
                "window_start_epoch": t.window_start_epoch,
                "drift_used": t.drift_used}
            for k, t in state.traj}
    charter = None
    if state.charter is not None:
        c = state.charter
        charter = {"granted_epoch": c.granted_epoch, "ttl": c.ttl,
                   "revoked": c.revoked, "policy_pin": c.policy_pin}
    pending = None
    if state.pending is not None:
        pending = {"deltas": {k: v for k, v in state.pending.deltas},
                   "proposed_epoch": state.pending.proposed_epoch}
    return {"params": {k: v for k, v in state.params}, "traj": traj,
            "charter": charter, "frozen": state.frozen, "pending": pending}


def _step(
    state: ge.GovEpochState | None, op: str, args: dict[str, object],
) -> tuple[ge.GovEpochState, ge.GovReceipt | None]:
    from typing import Any, cast
    if op == "genesis":
        return ge.genesis_state(dict(cast(dict[str, int], args["params"])),
                                epoch=cast(int, args["epoch"])), None
    if op == "propose":
        assert state is not None
        out: tuple[Any, Any] = ge.propose_revision(state, dict(cast(dict[str, int], args["deltas"])),
                                   now_epoch=cast(int, args["now"]))
        return out
    if op == "veto":
        assert state is not None
        out = ge.veto_pending(state, now_epoch=cast(int, args["now"]))
        return out
    if op == "apply":
        assert state is not None
        out = ge.apply_pending(state, now_epoch=cast(int, args["now"]))
        return out
    if op == "renew":
        assert state is not None
        out = ge.renew_charter(state, now_epoch=cast(int, args["now"]),
                                ttl=cast(int, args["ttl"]), policy_pin=cast(str, args["pin"]))
        return out
    if op == "revoke":
        assert state is not None
        out = ge.revoke_charter(state, now_epoch=cast(int, args["now"]))
        return out
    if op == "freeze":
        assert state is not None
        out = ge.set_frozen(state, True, now_epoch=cast(int, args["now"]))
        return out
    if op == "unfreeze":
        assert state is not None
        out = ge.set_frozen(state, False, now_epoch=cast(int, args["now"]))
        return out
    raise ValueError(f"unknown op {op!r}")


def fixture_bytes() -> bytes:
    scenarios_out = []
    codes_seen: set[str] = set()
    gate_labels_seen: set[str] = set()
    for name, script in SCENARIOS:
        state: ge.GovEpochState | None = None
        steps_out: list[dict[str, object]] = []
        for op, args in script:
            new_state, receipt = _step(state, op, args)
            rec: dict[str, object] = {"op": op, "args": args}
            if receipt is not None:
                codes_seen.add(receipt.code)
                if receipt.code == ge.GOV_REJ_SURFACE_GATE and receipt.surface:
                    gate_labels_seen.add(receipt.surface)
                rec["receipt"] = {
                    "code": receipt.code, "epoch": receipt.epoch,
                    "surface": receipt.surface,
                    "digest_before": receipt.digest_before,
                    "digest_after": receipt.digest_after,
                    "policy_pin": receipt.policy_pin,
                }
            state = new_state
            rec["state"] = _observe(state)
            steps_out.append(rec)
        scenarios_out.append({"name": name, "steps": steps_out})

    all_codes = {v for k, v in vars(ge).items()
                 if k.startswith(("GOV_OK_", "GOV_REJ_")) and isinstance(v, str)}
    missing = sorted(all_codes - codes_seen)
    if missing:
        raise AssertionError(f"scenario corpus misses receipt codes: {missing}")
    expected_labels = {"fee_bps", "router", "collateral"}
    if not expected_labels <= gate_labels_seen:
        raise AssertionError(
            f"surface-gate labels missing: {sorted(expected_labels - gate_labels_seen)}")

    doc = {
        "comment": ("GENERATED by gen_rust_epoch_fixture.py — REPLAYED through gov_epoch.py;"
                    " do not edit by hand; test_gov_parity.py byte-pins this file. The Rust"
                    " epoch module must reproduce every recorded field per step."),
        "scenarios": scenarios_out,
    }
    return (json.dumps(doc, indent=1, sort_keys=False) + "\n").encode("utf-8")


def main() -> int:
    FIXTURE.parent.mkdir(parents=True, exist_ok=True)
    data = fixture_bytes()
    FIXTURE.write_bytes(data)
    n_steps = sum(len(s) for _, s in SCENARIOS)
    print(f"wrote {FIXTURE} ({len(data)} bytes, {len(SCENARIOS)} scenarios, {n_steps} steps,"
          " all receipt codes covered)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
