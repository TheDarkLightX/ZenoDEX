#!/usr/bin/env python3
"""Apply the exact, non-promoting ZRPF assurance repair for 2026-07-14."""

from __future__ import annotations

import re
from pathlib import Path


def replace_once(path: str, old: str, new: str) -> None:
    target = Path(path)
    text = target.read_text(encoding="utf-8")
    count = text.count(old)
    if count != 1:
        raise SystemExit(f"{path}: expected one replacement, observed {count}")
    target.write_text(text.replace(old, new, 1), encoding="utf-8")


def repair_retained_evidence_expectations() -> None:
    for path in (
        "tests/test_check_zrpf_v1_spot_adapter_temporary_evidence.py",
        "tests/test_check_zrpf_v3_structural_tree_temporary_evidence.py",
    ):
        replace_once(
            path,
            '        "source SHA-256 mismatch: zk/state_proof_risc0/shared/Cargo.toml",\n',
            '        "source SHA-256 mismatch: zk/state_proof_risc0/shared/Cargo.toml",\n'
            '        "source SHA-256 mismatch: zk/state_proof_risc0/shared/src/lib.rs",\n',
        )
        replace_once(
            path,
            '        "source SHA-256 mismatch: zk/zrpf_risc0/shared/Cargo.toml",\n',
            '        "source SHA-256 mismatch: zk/zrpf_risc0/shared/Cargo.toml",\n'
            '        "source SHA-256 mismatch: zk/zrpf_risc0/shared/src/lib.rs",\n'
            '        "source SHA-256 mismatch: zk/zrpf_risc0/shared/src/v1_leaf_adapter.rs",\n',
        )


def repair_source_inventory() -> None:
    checkpoint_rows = '''    (
        "checkpoint_finality_protocol_v1",
        "zk/zrpf_protocol/protocol/src/checkpoint_finality_v1/certificate.rs",
    ),
    (
        "checkpoint_finality_protocol_v1",
        "zk/zrpf_protocol/protocol/src/checkpoint_finality_v1/codec.rs",
    ),
    (
        "checkpoint_finality_protocol_v1",
        "zk/zrpf_protocol/protocol/src/checkpoint_finality_v1/error.rs",
    ),
    (
        "checkpoint_finality_protocol_v1",
        "zk/zrpf_protocol/protocol/src/checkpoint_finality_v1/hash.rs",
    ),
    (
        "checkpoint_finality_protocol_v1",
        "zk/zrpf_protocol/protocol/src/checkpoint_finality_v1/mod.rs",
    ),
    (
        "checkpoint_finality_protocol_v1",
        "zk/zrpf_protocol/protocol/src/checkpoint_finality_v1/policy.rs",
    ),
    (
        "checkpoint_finality_protocol_v2",
        "zk/zrpf_protocol/protocol/src/checkpoint_finality_v2/certificate.rs",
    ),
    (
        "checkpoint_finality_protocol_v2",
        "zk/zrpf_protocol/protocol/src/checkpoint_finality_v2/codec.rs",
    ),
    (
        "checkpoint_finality_protocol_v2",
        "zk/zrpf_protocol/protocol/src/checkpoint_finality_v2/cursor.rs",
    ),
    (
        "checkpoint_finality_protocol_v2",
        "zk/zrpf_protocol/protocol/src/checkpoint_finality_v2/error.rs",
    ),
    (
        "checkpoint_finality_protocol_v2",
        "zk/zrpf_protocol/protocol/src/checkpoint_finality_v2/hash.rs",
    ),
    (
        "checkpoint_finality_protocol_v2",
        "zk/zrpf_protocol/protocol/src/checkpoint_finality_v2/mod.rs",
    ),
    (
        "checkpoint_finality_protocol_v2",
        "zk/zrpf_protocol/protocol/src/checkpoint_finality_v2/policy.rs",
    ),
    (
        "checkpoint_finality_protocol_v2",
        "zk/zrpf_protocol/protocol/src/checkpoint_finality_v2/transition.rs",
    ),
    (
        "assurance_compiler_source",
        "zk/zrpf_protocol/protocol/tests/checkpoint_finality_v1.rs",
    ),
    (
        "assurance_compiler_source",
        "zk/zrpf_protocol/protocol/tests/checkpoint_finality_v2.rs",
    ),
'''
    replace_once(
        "tools/zrpf_v3_source_closure.py",
        '    (\n        "parallel_shard_epoch_protocol_v1",\n',
        checkpoint_rows + '    (\n        "parallel_shard_epoch_protocol_v1",\n',
    )
    replace_once(
        "tests/test_zrpf_v3_source_closure.py",
        '    assert document["file_count"] == 399\n',
        '    assert document["file_count"] == 415\n',
    )
    replace_once(
        "tests/test_zrpf_v3_source_closure.py",
        '    assert roles_by_path["zk/zrpf_protocol/protocol/src/full_blob_da_v1/policy.rs"] == (\n'
        '        "data_availability_protocol_v1"\n'
        '    )\n',
        '    assert roles_by_path["zk/zrpf_protocol/protocol/src/full_blob_da_v1/policy.rs"] == (\n'
        '        "data_availability_protocol_v1"\n'
        '    )\n'
        '    assert roles_by_path[\n'
        '        "zk/zrpf_protocol/protocol/src/checkpoint_finality_v2/transition.rs"\n'
        '    ] == "checkpoint_finality_protocol_v2"\n',
    )


def repair_darwin_limits() -> None:
    path = Path("tools/run_zrpf_source_opened_spot_v6_darwin_settlement_benchmark.py")
    text = path.read_text(encoding="utf-8")
    replacement = '''def _set_child_limit(resource_id: int, requested: int) -> None:
    """Install a limit no looser than requested under the inherited hard cap."""

    _soft, inherited_hard = resource.getrlimit(resource_id)
    effective = (
        requested
        if inherited_hard == resource.RLIM_INFINITY
        else min(requested, inherited_hard)
    )
    if effective < 0:
        raise WorkerError("inherited child resource limit is invalid")
    resource.setrlimit(resource_id, (effective, effective))


def _limit_child(limits: Mapping[str, object]) -> None:
    _set_child_limit(resource.RLIMIT_NOFILE, _recorded_int(limits, "max_open_files"))
    if hasattr(resource, "RLIMIT_NPROC"):
        _set_child_limit(resource.RLIMIT_NPROC, _recorded_int(limits, "max_processes"))
    if hasattr(resource, "RLIMIT_CORE"):
        _set_child_limit(resource.RLIMIT_CORE, 0)
    if hasattr(resource, "RLIMIT_AS"):
        _set_child_limit(
            resource.RLIMIT_AS,
            _recorded_int(limits, "max_virtual_address_space_bytes"),
        )
    if hasattr(resource, "RLIMIT_FSIZE"):
        _set_child_limit(
            resource.RLIMIT_FSIZE,
            _recorded_int(limits, "max_stage_artifact_bytes"),
        )
    os.umask(0o077)


'''
    text, count = re.subn(
        r"def _limit_child\(limits: Mapping\[str, object\]\) -> None:\n.*?(?=def _kill_residual_process_group)",
        replacement,
        text,
        count=1,
        flags=re.DOTALL,
    )
    if count != 1:
        raise SystemExit(f"Darwin limit replacement count: {count}")
    path.write_text(text, encoding="utf-8")


def repair_profile_depth_guard() -> None:
    path = Path("tools/check_zrpf_v3_firecracker_replay_profile.py")
    text = path.read_text(encoding="utf-8")
    helper = '''def _require_bounded_json_depth(raw: bytes, maximum: int = 128) -> None:
    depth = 0
    in_string = False
    escaped = False
    for byte in raw:
        if in_string:
            if escaped:
                escaped = False
            elif byte == 0x5C:
                escaped = True
            elif byte == 0x22:
                in_string = False
            continue
        if byte == 0x22:
            in_string = True
        elif byte in (0x5B, 0x7B):
            depth += 1
            if depth > maximum:
                raise ValueError("profile JSON exceeds the nesting limit")
        elif byte in (0x5D, 0x7D):
            depth -= 1
            if depth < 0:
                raise ValueError("profile JSON nesting is malformed")


'''
    marker = "def _validate_profile_document(\n"
    if text.count(marker) != 1:
        raise SystemExit("profile depth insertion marker mismatch")
    text = text.replace(marker, helper + marker, 1)
    old = (
        "        raw = _read_bounded_regular(profile_path)\n"
        "        profile = support.strict_json_loads(raw)\n"
    )
    new = (
        "        raw = _read_bounded_regular(profile_path)\n"
        "        _require_bounded_json_depth(raw)\n"
        "        profile = support.strict_json_loads(raw)\n"
    )
    if text.count(old) != 1:
        raise SystemExit("profile parse replacement marker mismatch")
    path.write_text(text.replace(old, new, 1), encoding="utf-8")


def repair_authority_allowlist() -> None:
    path = Path("tests/integration/test_recursive_stark_admission_authority_boundary.py")
    text = path.read_text(encoding="utf-8")
    replace_once(
        str(path),
        'SPOT_V7_ATOMIC_STORE = (\n    ROOT / "src/integration/zrpf_spot_v7_atomic_settlement_store.py"\n)\n',
        'SPOT_V7_ATOMIC_STORE = (\n    ROOT / "src/integration/zrpf_spot_v7_atomic_settlement_store.py"\n)\n'
        'SPOT_V7_OPERATIONAL_CAPABILITY_V2 = (\n'
        '    ROOT / "src/integration/_zrpf_spot_v7_operational_capability_v2.py"\n'
        ')\n'
        'SPOT_V7_OPERATIONAL_GATE = (\n'
        '    ROOT / "src/integration/_zrpf_spot_v7_operational_gate.py"\n'
        ')\n',
    )
    replace_once(
        str(path),
        'PRIVATE_FIRECRACKER_STORE_REFERENCES = frozenset(\n'
        '    {\n'
        '        "_GovernedFirecrackerSpotV7SettlementV1",\n'
        '        "_require_governed_firecracker_spot_v7_authority_available_v1",\n'
        '    }\n'
        ')\n',
        'PRIVATE_FIRECRACKER_STORE_REFERENCES = frozenset(\n'
        '    {\n'
        '        "_GovernedFirecrackerSpotV7SettlementV1",\n'
        '        "_require_governed_firecracker_spot_v7_authority_available_v1",\n'
        '    }\n'
        ')\n'
        'PRIVATE_OPERATIONAL_FIRECRACKER_REFERENCES = frozenset(\n'
        '    {\n'
        '        "_GovernedFirecrackerSpotV7SettlementV1",\n'
        '        "_candidate_for_atomic_store",\n'
        '    }\n'
        ')\n',
    )
    replace_once(
        str(path),
        '            SPOT_V7_ATOMIC_STORE: PRIVATE_FIRECRACKER_STORE_REFERENCES,\n',
        '            SPOT_V7_ATOMIC_STORE: PRIVATE_FIRECRACKER_STORE_REFERENCES,\n'
        '            SPOT_V7_OPERATIONAL_CAPABILITY_V2: (\n'
        '                PRIVATE_OPERATIONAL_FIRECRACKER_REFERENCES\n'
        '            ),\n'
        '            SPOT_V7_OPERATIONAL_GATE: PRIVATE_OPERATIONAL_FIRECRACKER_REFERENCES,\n',
    )


def main() -> None:
    phases = (
        ("retained evidence expectations", repair_retained_evidence_expectations),
        ("source inventory", repair_source_inventory),
        ("Darwin resource limits", repair_darwin_limits),
        ("profile depth guard", repair_profile_depth_guard),
        ("authority allowlist", repair_authority_allowlist),
    )
    for label, phase in phases:
        print(f"applying {label}", flush=True)
        phase()
    print("ZRPF assurance repair applied", flush=True)


if __name__ == "__main__":
    main()
