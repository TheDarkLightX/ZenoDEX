#!/usr/bin/env python3
"""Build the disaster-axis status manifest (goal doc acceptance criterion: total axis coverage).

Derives one row per live axis in ``DISASTER_SEARCH_EXPANSION_AXES``:
``inductive_esso`` rows bind a committed ESSO model and its two-solver
verify-multi receipt by sha256; every other axis is ``bounded_replay`` (the
240-second replay lane documented in docs/DISASTER_STATE_COVERAGE.md).
The axis definition itself is pinned by the sha256 of its canonical JSON so
silent axis edits invalidate the manifest. Research-only; grants no authority.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from tools.stateful_scenario_bridge import DISASTER_SEARCH_EXPANSION_AXES  # noqa: E402

MANIFEST_SCHEMA_V1 = "zenodex/disaster-axis-status-manifest/v1"
MODEL_DIR = "experiments/disaster_inductive_promotion/models"
RECEIPT_DIR = "experiments/disaster_inductive_promotion/receipts"

# zusd_oracle_recovery_split_brain is deliberately NOT inductive_esso: the 2026-09-02
# independent review showed its oracle freshness/quorum guards are not load-bearing
# (all 15 deletable with VERIFIED preserved), so its model does not certify the axis.
INDUCTIVE_MODEL_BY_AXIS = {
    "batch_refinement_mci_parity_boundary": "disaster_batch_refinement_mci_parity_boundary_inductive_v1",
    "batch_settler_greedy_adapter_boundary": "disaster_batch_settler_greedy_adapter_boundary_inductive_v1",
    "dex_engine_sequence_anomaly_surface": "disaster_dex_engine_sequence_anomaly_surface_inductive_v1",
    "dex_settlement_recovery_proof_unit_boundary": "disaster_dex_settlement_recovery_v1",
    "perp_funding_liquidation_oracle_window": "disaster_perp_funding_liquidation_oracle_window_inductive_v1",
    "quote_receipt_gate_decomposition_consistency": "disaster_quote_receipt_gate_decomposition_consistency_inductive_v1",
    "reciprocal_netting_pair_forgery": "disaster_reciprocal_netting_pair_forgery_inductive_v1",
    "settlement_proof_recompute_gate": "disaster_settlement_proof_recompute_gate_inductive_v1",
    "state_accounting_size_boundary": "disaster_state_accounting_size_boundary_inductive_v1",
    "vault_reward_carry_spendability": "disaster_vault_reward_carry_spendability_inductive_v1",
    "zusd_native_accounting_gate_boundary": "disaster_zusd_native_accounting_gate_boundary_inductive_v1",
}


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _axis_definition_sha(axis: dict) -> str:
    canonical = json.dumps(axis, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(canonical.encode("utf-8")).hexdigest()


def build_manifest(root: Path) -> dict:
    rows = []
    for axis in DISASTER_SEARCH_EXPANSION_AXES:
        axis_id = axis["axis_id"]
        row: dict[str, object] = {
            "axis_id": axis_id,
            "axis_definition_sha256": _axis_definition_sha(axis),
        }
        model_name = INDUCTIVE_MODEL_BY_AXIS.get(axis_id)
        if model_name is not None:
            model = root / MODEL_DIR / f"{model_name}.yaml"
            receipt = root / RECEIPT_DIR / f"{model_name}.verify_multi.json"
            row["status"] = "inductive_esso"
            row["model_path"] = f"{MODEL_DIR}/{model_name}.yaml"
            row["model_sha256"] = _sha256(model)
            row["receipt_path"] = f"{RECEIPT_DIR}/{model_name}.verify_multi.json"
            row["receipt_sha256"] = _sha256(receipt)
        elif axis_id == "zusd_oracle_recovery_split_brain":
            row["status"] = "bounded_replay"
            row["evidence_note"] = (
                "downgraded from inductive_esso by independent review 2026-09-02: the authored "
                "model's oracle freshness/quorum guards are jointly deletable with VERIFIED "
                "preserved, so the inductive certificate does not certify this axis's semantics; "
                "bounded 240s replay lane only until the model is strengthened"
            )
        else:
            row["status"] = "bounded_replay"
            row["evidence_note"] = (
                "bounded 240s replay lane (docs/DISASTER_STATE_COVERAGE.md); receipt is a "
                "local git-ignored artifact and is not CI-enforced"
            )
        rows.append(row)
    return {
        "schema": MANIFEST_SCHEMA_V1,
        "status_vocabulary": ["inductive_esso", "lean", "tau", "bounded_replay", "open", "out_of_scope"],
        "axis_count": len(rows),
        "rows": rows,
        "nonclaims": [
            "A bounded_replay row is bounded evidence only: it certifies the axis's commands "
            "replayed green under a 240-second budget on one machine, not unreachability in general.",
            "An inductive_esso row certifies the bounded model's invariants are inductive under "
            "z3 and cvc5 agreement; it does not refine the running implementation.",
            "No production, release, settlement, verifier, migration, publication, or "
            "value-moving authority is granted.",
        ],
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", default=str(REPO_ROOT))
    parser.add_argument("--output", default="tools/disaster_axis_status_manifest.json")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    root = Path(args.root).resolve()
    manifest = build_manifest(root)
    rendered = json.dumps(manifest, indent=2, sort_keys=False) + "\n"
    target = root / args.output
    if args.check:
        if not target.is_file() or target.read_text(encoding="utf-8") != rendered:
            print(json.dumps({"ok": False, "mode": "check", "detail": "manifest drift"}))
            return 1
        print(json.dumps({"ok": True, "mode": "check", "axis_count": manifest["axis_count"]}))
        return 0
    target.write_text(rendered, encoding="utf-8")
    print(json.dumps({"ok": True, "mode": "write", "axis_count": manifest["axis_count"]}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
