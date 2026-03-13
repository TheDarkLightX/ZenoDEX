#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Mapping

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from tools.check_tau_formal_plan import DEFAULT_PLAN


DEFAULT_SEMANTIC_VIEW = REPO_ROOT / "formal" / "tau" / "recommended_semantic_view.json"
DEFAULT_OUT_JSON = REPO_ROOT / "formal" / "tau" / "scaffolds" / "contract_draft_bundle.json"


def _load_json(path: Path) -> dict[str, Any]:
    raw = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(raw, dict):
        raise ValueError(f"{path}: expected JSON object")
    return raw


def _sort_stream_name(name: str) -> tuple[int, str]:
    suffix = name[1:]
    if suffix.isdigit():
        return int(suffix), name
    return 10**9, name


def _slot_type(ty: str) -> str:
    compact = ty.replace("[", "").replace("]", "")
    mapping = {
        "sbf": "sbf",
        "bv16": "bv16",
        "bv32": "bv32",
        "bv64": "bv64",
    }
    return mapping.get(compact, "bv32")


def _kind_from_profile(profile_id: str) -> str:
    if profile_id == "proof_gate_or_certificate":
        return "proof_gate"
    if profile_id == "bundle_or_composition":
        return "bundle_or_composition"
    if profile_id == "stateful_policy_guard":
        return "stateful_policy_guard"
    return "combinational_guard"


def _profile_index(plan: Mapping[str, Any]) -> dict[str, Mapping[str, Any]]:
    out: dict[str, Mapping[str, Any]] = {}
    for profile in plan.get("profiles", []):
        if not isinstance(profile, Mapping):
            continue
        profile_id = str(profile.get("id", "")).strip()
        if profile_id:
            out[profile_id] = profile
    return out


def _all_sbf(packet: Mapping[str, Any]) -> bool:
    input_streams = packet.get("input_streams", {})
    if not isinstance(input_streams, Mapping) or not input_streams:
        return False
    return all(str(ty) == "sbf" for ty in input_streams.values())


def _make_lightweight_draft(packet: Mapping[str, Any]) -> dict[str, Any]:
    spec_id = str(packet["spec_id"])
    input_streams = packet.get("input_streams", {})
    output_streams = packet.get("output_streams", {})
    sorted_inputs = sorted((str(name), str(ty)) for name, ty in input_streams.items())
    sorted_outputs = sorted((str(name), str(ty)) for name, ty in output_streams.items())
    zero_step = {name: 0 for name, _ in sorted_inputs}
    zero_expected = {name: 0 for name, _ in sorted_outputs}

    return {
        "contract_id": f"{spec_id}_semantic_draft_v1",
        "spec_path": str(packet["spec_path"]),
        "run_mode": "repl",
        "style": "host_projected_boolean_gate" if _all_sbf(packet) else "native_tau_guard",
        "summary": f"DRAFT scaffold for {spec_id}. Replace placeholder assumptions/guarantees before activation.",
        "control_inputs": [
            {
                "slot": name,
                "name": f"{name}_todo",
                "meaning": f"TODO: define semantic meaning for {name}",
            }
            for name, ty in sorted_inputs
            if ty == "sbf"
        ],
        "data_inputs": [
            {
                "slot": name,
                "name": f"{name}_todo",
                "meaning": f"TODO: define semantic meaning for {name}",
            }
            for name, ty in sorted_inputs
            if ty != "sbf"
        ],
        "outputs": [
            {
                "slot": name,
                "name": f"{name}_todo",
                "meaning": f"TODO: define semantic meaning for {name}",
            }
            for name, _ in sorted_outputs
        ],
        "assumptions": [
            "TODO: declare host/protocol assumptions for this spec.",
        ],
        "non_goals": [
            "TODO: declare what this Tau spec intentionally does not prove.",
        ],
        "guarantees": [
            {
                "id": "G_draft_placeholder",
                "description": "TODO: replace with real guarantees.",
                "cases": [
                    {
                        "id": "draft_accept_placeholder",
                        "steps": [zero_step],
                        "expected": [zero_expected],
                    }
                ],
            }
        ],
        "forbidden_behaviors": [
            {
                "id": "F_draft_placeholder",
                "description": "TODO: replace with real forbidden behavior cases.",
                "cases": [
                    {
                        "id": "draft_reject_placeholder",
                        "steps": [zero_step],
                        "expected": [zero_expected],
                    }
                ],
            }
        ],
    }


def _make_formal_contract_draft(packet: Mapping[str, Any], profile: Mapping[str, Any]) -> dict[str, Any]:
    spec_id = str(packet["spec_id"])
    profile_id = str(packet["profile"])
    kind = _kind_from_profile(profile_id)
    input_streams = packet.get("input_streams", {})
    output_streams = packet.get("output_streams", {})
    all_sbf = _all_sbf(packet)
    proof_scope = "full_input_domain" if all_sbf and profile_id == "exact_combinational_guard" else "bounded_assurance_domain"

    outputs = []
    for name, ty in sorted(((str(k), str(v)) for k, v in output_streams.items()), key=lambda item: _sort_stream_name(item[0])):
        outputs.append(
            {
                "name": name,
                "type": _slot_type(ty),
                "meaning": f"TODO: define semantic meaning for {name}",
                "contract_formula": f"TODO: formal definition for {name}",
                "contract_expr": "0",
            }
        )

    required_theorems = profile.get("required_theorems", [])
    if not isinstance(required_theorems, list):
        required_theorems = []
    preferred_stack = profile.get("mechanization_stack", [])
    if not isinstance(preferred_stack, list):
        preferred_stack = []
    theorem_rows = []
    for theorem_kind in required_theorems:
        if not isinstance(theorem_kind, str):
            continue
        theorem_rows.append(
            {
                "id": f"{theorem_kind}_todo",
                "kind": theorem_kind,
                "statement": f"TODO: state {theorem_kind} theorem for {spec_id}.",
                "preferred_mechanization": preferred_stack,
            }
        )

    return {
        "schema": "zenodex/tau/spec-contract/v1",
        "spec_id": spec_id,
        "spec_path": str(packet["spec_path"]),
        "kind": kind,
        "contract_status": "draft",
        "proof_scope": proof_scope,
        "human_summary": f"DRAFT scaffold for {spec_id} ({profile_id}).",
        "assumptions": [
            "TODO: declare explicit assumptions for the contract.",
        ],
        "input_domain": {
            "streams": [
                {
                    "name": str(name),
                    "type": _slot_type(str(ty)),
                    "role": f"{name}_todo",
                }
                for name, ty in sorted(((str(k), str(v)) for k, v in input_streams.items()), key=lambda item: _sort_stream_name(item[0]))
            ],
            "domain_model": "total_bitvector_product",
            "intended_preconditions": [
                "TODO: add intended preconditions for this spec.",
            ],
            "analysis_partitions": [
                {
                    "id": "todo_partition",
                    "formula": "TODO",
                    "intent": "TODO",
                }
            ],
        },
        "outputs": outputs,
        "behavior_partition": {
            "partition_basis": "output_vector",
            "coverage_goal": "promotion_gate",
            "reachable_vectors_must_be_witnessed": True,
            "unreachable_vectors_must_be_proved": True,
        },
        "theorems": theorem_rows or [
            {
                "id": "theorem_todo",
                "kind": "exactness",
                "statement": f"TODO: add required theorem obligations for {spec_id}.",
                "preferred_mechanization": preferred_stack,
            }
        ],
    }


def _make_atlas_draft(packet: Mapping[str, Any], contract: Mapping[str, Any]) -> dict[str, Any]:
    output_order = sorted((str(name) for name in packet.get("output_streams", {}).keys()), key=_sort_stream_name)
    spec_id = str(packet["spec_id"])
    return {
        "schema": "zenodex/tau/behavior-atlas/v1",
        "spec_id": spec_id,
        "spec_path": str(packet["spec_path"]),
        "contract_ref": f"formal/tau/contracts/{spec_id}.contract.json",
        "atlas_status": "draft",
        "proof_scope": str(contract["proof_scope"]),
        "output_order": output_order,
        "regions": [],
        "partition_checks": {
            "disjointness": "pending",
            "exhaustiveness": "pending",
            "tau_differential": "pending",
            "interpreter_equivalence": "pending",
        },
    }


def build_scaffold_bundle(
    *,
    semantic_view: Mapping[str, Any],
    proof_plan: Mapping[str, Any],
    include_spec_ids: set[str] | None = None,
) -> dict[str, Any]:
    profiles = _profile_index(proof_plan)
    packets = semantic_view.get("packets", [])
    if not isinstance(packets, list):
        raise ValueError("semantic view packets must be a list")

    lightweight_drafts: list[dict[str, Any]] = []
    formal_drafts: list[dict[str, Any]] = []
    atlas_drafts: list[dict[str, Any]] = []

    for packet in packets:
        if not isinstance(packet, Mapping):
            continue
        spec_id = str(packet.get("spec_id", "")).strip()
        if not spec_id:
            continue
        if include_spec_ids is not None and spec_id not in include_spec_ids:
            continue

        if _all_sbf(packet):
            lightweight_drafts.append(_make_lightweight_draft(packet))

        profile_id = str(packet.get("profile", "")).strip()
        profile = profiles.get(profile_id, {})
        formal_contract = _make_formal_contract_draft(packet, profile)
        formal_drafts.append(formal_contract)
        atlas_drafts.append(_make_atlas_draft(packet, formal_contract))

    return {
        "schema": "zenodex/tau/contract-scaffold-bundle/v1",
        "source_semantic_view": str(semantic_view.get("execution_census_ref", "")),
        "spec_count": len(formal_drafts),
        "lightweight_draft_count": len(lightweight_drafts),
        "formal_contract_draft_count": len(formal_drafts),
        "formal_atlas_draft_count": len(atlas_drafts),
        "lightweight_drafts": lightweight_drafts,
        "formal_contract_drafts": formal_drafts,
        "formal_atlas_drafts": atlas_drafts,
    }


def _write_per_spec_formal_files(
    *,
    bundle: Mapping[str, Any],
    contracts_out_dir: Path,
    atlases_out_dir: Path,
) -> None:
    contracts_out_dir.mkdir(parents=True, exist_ok=True)
    atlases_out_dir.mkdir(parents=True, exist_ok=True)
    contracts = bundle.get("formal_contract_drafts", [])
    atlases = bundle.get("formal_atlas_drafts", [])
    if not isinstance(contracts, list) or not isinstance(atlases, list):
        raise ValueError("invalid scaffold bundle")

    atlas_by_id = {
        str(row.get("spec_id", "")).strip(): row
        for row in atlases
        if isinstance(row, Mapping) and str(row.get("spec_id", "")).strip()
    }
    for contract in contracts:
        if not isinstance(contract, Mapping):
            continue
        spec_id = str(contract.get("spec_id", "")).strip()
        if not spec_id:
            continue
        contract_path = contracts_out_dir / f"{spec_id}.contract.json"
        contract_path.write_text(json.dumps(contract, indent=2) + "\n", encoding="utf-8")
        atlas = atlas_by_id.get(spec_id, {})
        atlas_path = atlases_out_dir / f"{spec_id}.atlas.json"
        atlas_path.write_text(json.dumps(atlas, indent=2) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Scaffold Tau semantic/proof contract drafts from semantic-view packets.")
    parser.add_argument("--semantic-view", default=str(DEFAULT_SEMANTIC_VIEW), help="Path to semantic-view JSON.")
    parser.add_argument("--plan", default=str(DEFAULT_PLAN), help="Path to Tau proof-plan JSON.")
    parser.add_argument("--spec-id", action="append", default=[], help="Optional spec ids to scaffold.")
    parser.add_argument("--out-json", default=str(DEFAULT_OUT_JSON), help="Path to scaffold bundle output JSON.")
    parser.add_argument(
        "--write-per-spec-formal-files",
        action="store_true",
        help="Also emit per-spec draft contract and atlas files.",
    )
    parser.add_argument(
        "--contracts-out-dir",
        default=str(REPO_ROOT / "formal" / "tau" / "scaffolds" / "contracts"),
        help="Output directory for per-spec contract drafts.",
    )
    parser.add_argument(
        "--atlases-out-dir",
        default=str(REPO_ROOT / "formal" / "tau" / "scaffolds" / "atlases"),
        help="Output directory for per-spec atlas drafts.",
    )
    args = parser.parse_args()

    semantic_view = _load_json(Path(args.semantic_view))
    proof_plan = _load_json(Path(args.plan))
    include_ids = {value.strip() for value in args.spec_id if value.strip()} or None
    bundle = build_scaffold_bundle(
        semantic_view=semantic_view,
        proof_plan=proof_plan,
        include_spec_ids=include_ids,
    )

    out_path = Path(args.out_json)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(bundle, indent=2) + "\n", encoding="utf-8")
    print(f"spec scaffolds: {bundle['spec_count']}")
    print(f"lightweight drafts: {bundle['lightweight_draft_count']}")
    print(f"formal contract drafts: {bundle['formal_contract_draft_count']}")
    print(f"formal atlas drafts: {bundle['formal_atlas_draft_count']}")
    print(f"wrote {out_path}")

    if args.write_per_spec_formal_files:
        _write_per_spec_formal_files(
            bundle=bundle,
            contracts_out_dir=Path(args.contracts_out_dir),
            atlases_out_dir=Path(args.atlases_out_dir),
        )
        print(f"wrote per-spec contract drafts to {Path(args.contracts_out_dir)}")
        print(f"wrote per-spec atlas drafts to {Path(args.atlases_out_dir)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
