#!/usr/bin/env python3
from __future__ import annotations

import importlib.util
import json
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]


@dataclass(frozen=True)
class DisasterCase:
    model_path: str
    model_id: str
    disaster_id: str
    description: str
    predecessor_trace: tuple[tuple[str, dict[str, Any]], ...]
    discharge_action: tuple[str, dict[str, Any]]
    expected_phase: str = "Complete"


CATALOG: tuple[DisasterCase, ...] = (
    DisasterCase(
        model_path="src/kernels/dex/sealed_bid_commit_reveal_gate_v1.yaml",
        model_id="sealed_bid_commit_reveal_gate_v1",
        disaster_id="empty_auction_deadlock",
        description="No bids were committed and the auction window closed; the FSM must still be able to terminate.",
        predecessor_trace=(
            ("advance_epoch", {"delta": 4}),
            ("advance_epoch", {"delta": 4}),
            ("advance_epoch", {"delta": 4}),
            ("advance_epoch", {"delta": 4}),
            ("advance_epoch", {"delta": 4}),
            ("advance_epoch", {"delta": 4}),
            ("advance_epoch", {"delta": 4}),
            ("advance_epoch", {"delta": 3}),
        ),
        discharge_action=("finalize_empty_auction", {}),
    ),
    DisasterCase(
        model_path="src/kernels/dex/sealed_bid_commit_reveal_gate_v1.yaml",
        model_id="sealed_bid_commit_reveal_gate_v1",
        disaster_id="no_reveal_deadlock",
        description="At least one commitment was posted but nobody revealed; the FSM must terminate without opening settlement.",
        predecessor_trace=(
            ("commit_bid", {"commitment_bound": True}),
            ("advance_epoch", {"delta": 2}),
            ("open_reveal", {}),
            ("advance_epoch", {"delta": 4}),
            ("advance_epoch", {"delta": 4}),
            ("advance_epoch", {"delta": 4}),
            ("advance_epoch", {"delta": 4}),
            ("advance_epoch", {"delta": 4}),
            ("advance_epoch", {"delta": 4}),
            ("advance_epoch", {"delta": 4}),
            ("advance_epoch", {"delta": 1}),
        ),
        discharge_action=("finalize_no_reveal_auction", {}),
    ),
    DisasterCase(
        model_path="src/kernels/dex/sealed_bid_non_reveal_bond_v1.yaml",
        model_id="sealed_bid_non_reveal_bond_v1",
        disaster_id="empty_bond_deadlock",
        description="No bonded commits were posted and the commit window closed; bond accounting must still complete.",
        predecessor_trace=(
            ("advance_epoch", {"delta": 4}),
            ("advance_epoch", {"delta": 4}),
            ("advance_epoch", {"delta": 4}),
            ("advance_epoch", {"delta": 4}),
            ("advance_epoch", {"delta": 4}),
            ("advance_epoch", {"delta": 4}),
            ("advance_epoch", {"delta": 4}),
            ("advance_epoch", {"delta": 3}),
        ),
        discharge_action=("finalize_empty_bonds", {}),
    ),
)


def _export_ref(model_path: str) -> Path:
    with tempfile.TemporaryDirectory(prefix="sealed_bid_catalog_") as tmp_dir:
        out_dir = Path(tmp_dir)
        cmd = [
            "python3",
            "-m",
            "ESSO",
            "export-python",
            model_path,
            "--output",
            str(out_dir),
        ]
        proc = subprocess.run(cmd, cwd=str(ROOT), capture_output=True, text=True)
        if proc.returncode != 0:
            raise RuntimeError(f"export-python failed for {model_path}: {proc.stderr.strip() or proc.stdout.strip()}")
        payload = json.loads(proc.stdout.strip())
        ref_path = ROOT / payload["files"]["model"]
        cached = ROOT / "generated" / "sealed_bid_catalog"
        cached.mkdir(parents=True, exist_ok=True)
        stable = cached / ref_path.name
        stable.write_text(ref_path.read_text(encoding="utf-8"), encoding="utf-8")
        return stable


def _load_ref(module_name: str, ref_path: Path) -> Any:
    spec = importlib.util.spec_from_file_location(module_name, ref_path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"could not load ref from {ref_path}")
    mod = importlib.util.module_from_spec(spec)
    sys.modules[module_name] = mod
    spec.loader.exec_module(mod)
    return mod


def _all_commands(mod: Any) -> list[Any]:
    model_name = Path(mod.__file__).name
    if model_name == "sealed_bid_commit_reveal_gate_v1_ref.py":
        commands: list[Any] = [mod.Command("open_reveal", {}), mod.Command("open_settlement", {}), mod.Command("finalize_auction", {}), mod.Command("finalize_empty_auction", {}), mod.Command("finalize_no_reveal_auction", {})]
        commands.extend(mod.Command("advance_epoch", {"delta": delta}) for delta in range(1, 5))
        commands.extend(mod.Command("commit_bid", {"commitment_bound": b}) for b in (False, True))
        commands.extend(
            mod.Command("reveal_bid", {"reveal_units": units, "commitment_match": cm, "nonce_unused": nu})
            for units in range(1, 32)
            for cm in (False, True)
            for nu in (False, True)
        )
        commands.extend(mod.Command("fill_units", {"fill_units": units}) for units in range(1, 32))
        return commands
    if model_name == "sealed_bid_non_reveal_bond_v1_ref.py":
        commands = [mod.Command("open_reveal", {}), mod.Command("open_slash", {}), mod.Command("slash_one_non_reveal", {}), mod.Command("finalize_bonds", {}), mod.Command("finalize_empty_bonds", {})]
        commands.extend(mod.Command("advance_epoch", {"delta": delta}) for delta in range(1, 5))
        commands.extend(mod.Command("post_bonded_commit", {"commitment_bound": b}) for b in (False, True))
        commands.extend(
            mod.Command("reveal_and_refund", {"commitment_match": cm, "nonce_unused": nu})
            for cm in (False, True)
            for nu in (False, True)
        )
        return commands
    raise ValueError(f"unsupported ref module: {model_name}")


def _run_trace(mod: Any, trace: tuple[tuple[str, dict[str, Any]], ...]) -> Any:
    state = mod.init_state()
    for idx, (tag, args) in enumerate(trace, 1):
        res = mod.step(state, mod.Command(tag, args))
        if not res.ok or res.state is None:
            raise RuntimeError(f"trace step {idx} failed for {tag}: {res.error}")
        state = res.state
    return state


def _accepted_command_tags(mod: Any, state: Any) -> list[str]:
    accepted: list[str] = []
    for cmd in _all_commands(mod):
        res = mod.step(state, cmd)
        if res.ok:
            accepted.append(str(cmd.tag))
    return sorted(set(accepted))


def generate_catalog() -> dict[str, Any]:
    ref_cache: dict[str, Any] = {}
    rows: list[dict[str, Any]] = []
    ok = True
    for case in CATALOG:
        ref_path = ref_cache.get(case.model_path)
        if ref_path is None:
            ref_path = _export_ref(case.model_path)
            ref_cache[case.model_path] = ref_path
        mod = _load_ref(f"sealed_bid_catalog.{case.model_id}.{case.disaster_id}", ref_path)
        predecessor = _run_trace(mod, case.predecessor_trace)
        accepted_before = _accepted_command_tags(mod, predecessor)
        discharge = mod.step(predecessor, mod.Command(case.discharge_action[0], case.discharge_action[1]))
        discharged = bool(discharge.ok and discharge.state is not None and getattr(discharge.state, "phase", None) == case.expected_phase)
        only_discharge_remains = accepted_before == [case.discharge_action[0]]
        row = {
            "model_id": case.model_id,
            "disaster_id": case.disaster_id,
            "description": case.description,
            "predecessor_trace_len": len(case.predecessor_trace),
            "accepted_before_discharge": accepted_before,
            "discharge_action": case.discharge_action[0],
            "discharged": discharged,
            "only_discharge_remains": only_discharge_remains,
            "final_phase": getattr(discharge.state, "phase", None) if discharge.state is not None else None,
            "error": None if discharge.ok else discharge.error,
        }
        rows.append(row)
        ok = ok and discharged and only_discharge_remains
    return {
        "schema": "zenodex/sealed-bid-disaster-catalog/v1",
        "ok": ok,
        "cases": rows,
    }


def main() -> int:
    payload = generate_catalog()
    print(json.dumps(payload, indent=2, sort_keys=True))
    return 0 if payload["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
