#!/usr/bin/env python3
"""Build a ZenoLedger manifest from arbitrary feature-test body files."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.integration.zeno_ledger_profile import validate_zeno_ledger_profile_v0
from src.integration.zeno_ledger_v0 import hash_v0, validate_body_v0


REPORT_SCHEMA = "zenodex.zeno_ledger.make_feature_lane_report.v0"
MANIFEST_SCHEMA = "zenodex.zeno_ledger.testnet_bundle.v0"
RETIRED_TAU_APP_STATE_SELECTOR_ERROR = "RETIRED_TAU_APP_STATE_SELECTOR"
RETIRED_TAU_BRIDGE_COMPANION_SELECTOR_ERROR = "RETIRED_TAU_BRIDGE_COMPANION_SELECTOR"
PATH_VALUE_FLAGS = {
    "--attestation",
    "--autotrader-state",
    "--bodies-dir",
    "--body",
    "--checkpoints-dir",
    "--confidential-state",
    "--headers-dir",
    "--index",
    "--manifest",
    "--mirror-root",
    "--oracle-reporter-state",
    "--oracle-state",
    "--out",
    "--out-dir",
    "--perp-state",
    "--prev-header",
    "--prev-snapshot",
    "--profile",
    "--proof-mining-state",
    "--source-root",
    "--tau-app-state",
    "--tau-chain-balances",
    "--upba-state",
    "--zusd-state",
    "--pre-snapshot",
}


def _load_json_object(path: Path) -> Mapping[str, Any]:
    obj = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(obj, Mapping):
        raise ValueError(f"{path} must decode to a JSON object")
    return obj


def _write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _rel(root: Path, path: Path) -> str:
    rel = path.resolve().relative_to(root.resolve()).as_posix()
    return rel if rel else "."


def _relativize_command(command: list[str], *, root: Path) -> list[str]:
    out: list[str] = []
    previous = ""
    for index, item in enumerate(command):
        if index == 0 and item == sys.executable:
            out.append("python3")
        elif previous in PATH_VALUE_FLAGS:
            path = Path(item)
            candidates = [path] if path.is_absolute() else [ROOT / path, path]
            for candidate in candidates:
                try:
                    out.append(_rel(root, candidate))
                    break
                except ValueError:
                    continue
            else:
                out.append(item)
        else:
            out.append(item)
        previous = item
    return out


def _relativize_optional_path(root: Path, path: Path | None) -> str | None:
    return None if path is None else _rel(root, path)


def _default_module_versions_digest() -> str:
    return hash_v0("feature_lane_module_versions", {"schema": "zeno_ledger_v0"})


def _load_and_validate_bodies(body_paths: list[Path]) -> list[dict[str, Any]]:
    if not body_paths:
        raise ValueError("at least one --body is required")
    bodies: list[dict[str, Any]] = []
    seen_heights: set[int] = set()
    for path in body_paths:
        body = dict(_load_json_object(path))
        validate_body_v0(body)
        height = body["height"]
        if not isinstance(height, int) or isinstance(height, bool) or height < 0:
            raise ValueError("body height must be a non-negative int")
        if height in seen_heights:
            raise ValueError(f"duplicate body height: {height}")
        seen_heights.add(height)
        bodies.append(body)
    bodies.sort(key=lambda item: int(item["height"]))
    for index, body in enumerate(bodies):
        if index > 0 and int(body["height"]) != int(bodies[index - 1]["height"]) + 1:
            raise ValueError("body heights must be contiguous")
    return bodies


def _body_cutoff_time_ms(body: Mapping[str, Any]) -> int:
    ingress = body["ingress"]
    if not isinstance(ingress, Mapping):
        raise ValueError("body ingress must be a JSON object")
    cutoff = ingress["batch_cutoff"]
    if not isinstance(cutoff, Mapping):
        raise ValueError("batch_cutoff must be a JSON object")
    value = cutoff["cutoff_time_ms"]
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        raise ValueError("cutoff_time_ms must be a non-negative int")
    return value


def _validate_feature_gate_commands(commands: list[list[str]]) -> list[list[str]]:
    out: list[list[str]] = []
    for command_index, command in enumerate(commands):
        if not isinstance(command, list) or not command:
            raise ValueError(f"feature_gate_commands[{command_index}] must be a non-empty list")
        clean: list[str] = []
        for arg_index, item in enumerate(command):
            if not isinstance(item, str) or item == "":
                raise ValueError(
                    f"feature_gate_commands[{command_index}][{arg_index}] "
                    "must be a non-empty string"
                )
            clean.append(item)
        out.append(clean)
    return out


def _parse_feature_gate_command_json(raw: str) -> list[str]:
    value = json.loads(raw)
    if not isinstance(value, list) or not value:
        raise ValueError("--feature-gate-command-json must decode to a non-empty JSON string list")
    out: list[str] = []
    for index, item in enumerate(value):
        if not isinstance(item, str) or item == "":
            raise ValueError(f"--feature-gate-command-json[{index}] must be a non-empty string")
        out.append(item)
    return out


def build_feature_lane_manifest_v0(
    *,
    out_dir: Path,
    profile_path: Path,
    genesis_snapshot_path: Path | None,
    tau_app_state_path: Path | None,
    zusd_state_path: Path | None,
    perp_state_path: Path | None,
    oracle_state_path: Path | None,
    oracle_reporter_state_path: Path | None,
    upba_state_path: Path | None,
    proof_mining_state_path: Path | None,
    autotrader_state_path: Path | None,
    confidential_state_path: Path | None,
    tau_chain_balances_path: Path | None,
    tau_chain_id: str | None,
    tau_enable_faucet: bool,
    body_paths: list[Path],
    module_versions_digest: str,
    allow_missing_settlement: bool,
    disable_intent_signatures: bool,
    feature_gate_commands: list[list[str]] | None = None,
) -> dict[str, Any]:
    if tau_app_state_path is not None:
        raise ValueError(RETIRED_TAU_APP_STATE_SELECTOR_ERROR)
    if (
        tau_chain_balances_path is not None
        or tau_chain_id is not None
        or tau_enable_faucet
    ):
        raise ValueError(RETIRED_TAU_BRIDGE_COMPANION_SELECTOR_ERROR)
    profile = dict(_load_json_object(profile_path))
    validate_zeno_ledger_profile_v0(profile)
    mode_count = sum(
        value is not None
        for value in (
            genesis_snapshot_path,
            zusd_state_path,
            perp_state_path,
            oracle_state_path,
            oracle_reporter_state_path,
            upba_state_path,
            proof_mining_state_path,
            autotrader_state_path,
            confidential_state_path,
        )
    )
    if mode_count != 1:
        raise ValueError(
            "exactly one of --genesis-snapshot, --zusd-state, --perp-state, "
            "--oracle-state, --oracle-reporter-state, --upba-state, --proof-mining-state, "
            "--autotrader-state, or --confidential-state is required"
        )
    genesis: dict[str, Any] | None = None
    if genesis_snapshot_path is not None:
        genesis = dict(_load_json_object(genesis_snapshot_path))
    zusd_state: dict[str, Any] | None = None
    if zusd_state_path is not None:
        zusd_state = dict(_load_json_object(zusd_state_path))
    perp_state: dict[str, Any] | None = None
    if perp_state_path is not None:
        perp_state = dict(_load_json_object(perp_state_path))
    oracle_state: dict[str, Any] | None = None
    if oracle_state_path is not None:
        oracle_state = dict(_load_json_object(oracle_state_path))
    oracle_reporter_state: dict[str, Any] | None = None
    if oracle_reporter_state_path is not None:
        oracle_reporter_state = dict(_load_json_object(oracle_reporter_state_path))
    upba_state: dict[str, Any] | None = None
    if upba_state_path is not None:
        upba_state = dict(_load_json_object(upba_state_path))
    proof_mining_state: dict[str, Any] | None = None
    if proof_mining_state_path is not None:
        proof_mining_state = dict(_load_json_object(proof_mining_state_path))
    autotrader_state: dict[str, Any] | None = None
    if autotrader_state_path is not None:
        autotrader_state = dict(_load_json_object(autotrader_state_path))
    confidential_state: dict[str, Any] | None = None
    if confidential_state_path is not None:
        confidential_state = dict(_load_json_object(confidential_state_path))
    bodies = _load_and_validate_bodies(body_paths)
    gates = _validate_feature_gate_commands(feature_gate_commands or [])
    chain_id = str(profile["chain_id"])
    for body in bodies:
        if body["chain_id"] != chain_id:
            raise ValueError("body chain_id must match profile chain_id")

    config_digest = str(profile["accepted_config_digests"][0])
    sequencer_set_hash = str(profile["accepted_sequencer_set_hashes"][0])
    profile_out = out_dir / "profile.json"
    genesis_out = out_dir / "genesis_snapshot.json"
    zusd_state_out = out_dir / "zusd_state.json"
    perp_state_out = out_dir / "perp_state.json"
    oracle_state_out = out_dir / "oracle_state.json"
    oracle_reporter_state_out = out_dir / "oracle_reporter_state.json"
    upba_state_out = out_dir / "upba_state.json"
    proof_mining_state_out = out_dir / "proof_mining_state.json"
    autotrader_state_out = out_dir / "autotrader_state.json"
    confidential_state_out = out_dir / "confidential_state.json"
    bodies_dir = out_dir / "bodies"
    ledger_out_dir = out_dir / "ledger"
    feature_gate_report_path = out_dir / "feature_gate_report.json"
    attestation_path = out_dir / "watcher_attestations" / "feature_lane.json"
    mirror_index_path = out_dir / "mirror_index.json"
    manifest_path = out_dir / "manifest.json"

    body_out_paths: list[Path] = []
    for body in bodies:
        body_out = bodies_dir / f"{int(body['height'])}.json"
        _write_json(body_out, body)
        body_out_paths.append(body_out)
    _write_json(profile_out, profile)
    if genesis is not None:
        _write_json(genesis_out, genesis)
    if zusd_state is not None:
        _write_json(zusd_state_out, zusd_state)
    if perp_state is not None:
        _write_json(perp_state_out, perp_state)
    if oracle_state is not None:
        _write_json(oracle_state_out, oracle_state)
    if oracle_reporter_state is not None:
        _write_json(oracle_reporter_state_out, oracle_reporter_state)
    if upba_state is not None:
        _write_json(upba_state_out, upba_state)
    if proof_mining_state is not None:
        _write_json(proof_mining_state_out, proof_mining_state)
    if autotrader_state is not None:
        _write_json(autotrader_state_out, autotrader_state)
    if confidential_state is not None:
        _write_json(confidential_state_out, confidential_state)

    run_commands: list[list[str]] = []
    previous_height: int | None = None
    for index, body in enumerate(bodies):
        height = int(body["height"])
        command = [
            sys.executable,
            "tools/zeno_ledger_run_local.py",
            "--body",
            str(body_out_paths[index]),
            "--out-dir",
            str(ledger_out_dir),
            "--time-ms",
            str(_body_cutoff_time_ms(body)),
            "--sequencer-set-hash",
            sequencer_set_hash,
            "--config-digest",
            config_digest,
            "--module-versions-digest",
            module_versions_digest,
        ]
        if genesis is not None and index == 0:
            command.extend(["--pre-snapshot", str(genesis_out)])
        elif genesis is not None:
            command.extend(
                [
                    "--prev-header",
                    str(ledger_out_dir / "headers" / f"{previous_height}.json"),
                    "--pre-snapshot",
                    str(ledger_out_dir / "snapshots" / f"{previous_height}.json"),
                ]
            )
        elif zusd_state is not None and index == 0:
            command.extend(["--zusd-state", str(zusd_state_out)])
        elif zusd_state is not None:
            command.extend(
                [
                    "--prev-header",
                    str(ledger_out_dir / "headers" / f"{previous_height}.json"),
                    "--zusd-state",
                    str(ledger_out_dir / "zusd_states" / f"{previous_height}.json"),
                ]
            )
        elif perp_state is not None and index == 0:
            command.extend(["--perp-state", str(perp_state_out)])
        elif perp_state is not None:
            command.extend(
                [
                    "--prev-header",
                    str(ledger_out_dir / "headers" / f"{previous_height}.json"),
                    "--perp-state",
                    str(ledger_out_dir / "perp_states" / f"{previous_height}.json"),
                ]
            )
        elif oracle_state is not None and index == 0:
            command.extend(["--oracle-state", str(oracle_state_out)])
        elif oracle_state is not None:
            command.extend(
                [
                    "--prev-header",
                    str(ledger_out_dir / "headers" / f"{previous_height}.json"),
                    "--oracle-state",
                    str(ledger_out_dir / "oracle_states" / f"{previous_height}.json"),
                ]
            )
        elif oracle_reporter_state is not None and index == 0:
            command.extend(["--oracle-reporter-state", str(oracle_reporter_state_out)])
        elif oracle_reporter_state is not None:
            command.extend(
                [
                    "--prev-header",
                    str(ledger_out_dir / "headers" / f"{previous_height}.json"),
                    "--oracle-reporter-state",
                    str(ledger_out_dir / "oracle_reporter_states" / f"{previous_height}.json"),
                ]
            )
        elif upba_state is not None and index == 0:
            command.extend(["--upba-state", str(upba_state_out)])
        elif upba_state is not None:
            command.extend(
                [
                    "--prev-header",
                    str(ledger_out_dir / "headers" / f"{previous_height}.json"),
                    "--upba-state",
                    str(ledger_out_dir / "upba_states" / f"{previous_height}.json"),
                ]
            )
        elif proof_mining_state is not None and index == 0:
            command.extend(["--proof-mining-state", str(proof_mining_state_out)])
        elif proof_mining_state is not None:
            command.extend(
                [
                    "--prev-header",
                    str(ledger_out_dir / "headers" / f"{previous_height}.json"),
                    "--proof-mining-state",
                    str(ledger_out_dir / "proof_mining_states" / f"{previous_height}.json"),
                ]
            )
        elif autotrader_state is not None and index == 0:
            command.extend(["--autotrader-state", str(autotrader_state_out)])
        elif autotrader_state is not None:
            command.extend(
                [
                    "--prev-header",
                    str(ledger_out_dir / "headers" / f"{previous_height}.json"),
                    "--autotrader-state",
                    str(ledger_out_dir / "autotrader_states" / f"{previous_height}.json"),
                ]
            )
        elif confidential_state is not None and index == 0:
            command.extend(["--confidential-state", str(confidential_state_out)])
        else:
            command.extend(
                [
                    "--prev-header",
                    str(ledger_out_dir / "headers" / f"{previous_height}.json"),
                    "--confidential-state",
                    str(ledger_out_dir / "confidential_states" / f"{previous_height}.json"),
                ]
            )
        if allow_missing_settlement:
            command.append("--allow-missing-settlement")
        if disable_intent_signatures:
            command.append("--disable-intent-signatures")
        run_commands.append(command)
        previous_height = height

    from_height = int(bodies[0]["height"])
    to_height = int(bodies[-1]["height"])
    verify_command = [
        sys.executable,
        "tools/zeno_ledger_verify.py",
        "--headers-dir",
        str(ledger_out_dir / "headers"),
        "--bodies-dir",
        str(ledger_out_dir / "bodies"),
        "--checkpoints-dir",
        str(ledger_out_dir / "checkpoints"),
        "--profile",
        str(profile_out),
        "--from-height",
        str(from_height),
        "--to-height",
        str(to_height),
    ]
    attest_command = [
        sys.executable,
        "tools/zeno_ledger_attest.py",
        "--headers-dir",
        str(ledger_out_dir / "headers"),
        "--bodies-dir",
        str(ledger_out_dir / "bodies"),
        "--checkpoints-dir",
        str(ledger_out_dir / "checkpoints"),
        "--profile",
        str(profile_out),
        "--from-height",
        str(from_height),
        "--to-height",
        str(to_height),
        "--watcher-id",
        "feature-lane-watcher-0",
        "--observed-time-ms",
        str(_body_cutoff_time_ms(bodies[-1]) + 1_000),
        "--out",
        str(attestation_path),
    ]
    mirror_index_command = [
        sys.executable,
        "tools/zeno_ledger_make_mirror_index.py",
        "--manifest",
        str(manifest_path),
        "--mirror-root",
        str(out_dir),
        "--out",
        str(mirror_index_path),
    ]
    run_commands = [_relativize_command(command, root=out_dir) for command in run_commands]
    verify_command = _relativize_command(verify_command, root=out_dir)
    gates = [_relativize_command(command, root=out_dir) for command in gates]
    attest_command = _relativize_command(attest_command, root=out_dir)
    mirror_index_command = _relativize_command(mirror_index_command, root=out_dir)
    manifest = {
        "schema": MANIFEST_SCHEMA,
        "bundle_kind": "feature_lane",
        "chain_id": chain_id,
        "from_height": from_height,
        "to_height": to_height,
        "config_digest": config_digest,
        "module_versions_digest": module_versions_digest,
        "sequencer_set_hash": sequencer_set_hash,
        "profile_path": _rel(out_dir, profile_out),
        "execution_mode": (
            "snapshot"
            if genesis is not None
            else "zusd"
            if zusd_state is not None
            else "perp"
            if perp_state is not None
            else "oracle"
            if oracle_state is not None
            else "oracle_reporter"
            if oracle_reporter_state is not None
            else "upba"
            if upba_state is not None
            else "proof_mining"
            if proof_mining_state is not None
            else "autotrader"
            if autotrader_state is not None
            else "confidential"
        ),
        "genesis_snapshot_path": _relativize_optional_path(out_dir, genesis_out if genesis is not None else None),
        "tau_app_state_path": None,
        "zusd_state_path": _relativize_optional_path(out_dir, zusd_state_out if zusd_state is not None else None),
        "perp_state_path": _relativize_optional_path(out_dir, perp_state_out if perp_state is not None else None),
        "oracle_state_path": _relativize_optional_path(out_dir, oracle_state_out if oracle_state is not None else None),
        "oracle_reporter_state_path": (
            _rel(out_dir, oracle_reporter_state_out) if oracle_reporter_state is not None else None
        ),
        "upba_state_path": _relativize_optional_path(out_dir, upba_state_out if upba_state is not None else None),
        "proof_mining_state_path": _relativize_optional_path(
            out_dir,
            proof_mining_state_out if proof_mining_state is not None else None,
        ),
        "autotrader_state_path": _relativize_optional_path(
            out_dir,
            autotrader_state_out if autotrader_state is not None else None,
        ),
        "confidential_state_path": _relativize_optional_path(
            out_dir,
            confidential_state_out if confidential_state is not None else None,
        ),
        "tau_chain_balances_path": None,
        "tau_chain_id": None,
        "tau_enable_faucet": False,
        "body_paths": [_rel(out_dir, path) for path in body_out_paths],
        "ledger_out_dir": _rel(out_dir, ledger_out_dir),
        "run_commands": run_commands,
        "verify_command": verify_command,
        "feature_gate_commands": gates,
        "feature_gate_report_path": _rel(out_dir, feature_gate_report_path),
        "attest_command": attest_command,
        "attestation_path": _rel(out_dir, attestation_path),
        "mirror_index_command": mirror_index_command,
        "mirror_index_path": _rel(out_dir, mirror_index_path),
    }
    _write_json(manifest_path, manifest)
    return {
        "schema": REPORT_SCHEMA,
        "ok": True,
        "status": "accepted",
        "manifest_path": str(manifest_path),
        "manifest": manifest,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Build a ZenoLedger feature-lane manifest",
        allow_abbrev=False,
    )
    parser.add_argument("--out-dir", required=True, type=Path)
    parser.add_argument("--profile", required=True, type=Path)
    parser.add_argument("--genesis-snapshot", type=Path)
    parser.add_argument("--tau-app-state", type=Path)
    parser.add_argument("--zusd-state", type=Path)
    parser.add_argument("--perp-state", type=Path)
    parser.add_argument("--oracle-state", type=Path)
    parser.add_argument("--oracle-reporter-state", type=Path)
    parser.add_argument("--upba-state", type=Path)
    parser.add_argument("--proof-mining-state", type=Path)
    parser.add_argument("--autotrader-state", type=Path)
    parser.add_argument("--confidential-state", type=Path)
    parser.add_argument("--tau-chain-balances", type=Path)
    parser.add_argument("--tau-chain-id")
    parser.add_argument("--tau-enable-faucet", action="store_true")
    parser.add_argument("--body", required=True, action="append", type=Path)
    parser.add_argument("--module-versions-digest", default=_default_module_versions_digest())
    parser.add_argument("--allow-missing-settlement", action="store_true")
    parser.add_argument("--disable-intent-signatures", action="store_true")
    parser.add_argument(
        "--feature-gate-command-json",
        action="append",
        default=[],
        help="JSON string list command to run after ledger verification; may be repeated",
    )
    args = parser.parse_args(argv)

    try:
        feature_gate_commands = [
            _parse_feature_gate_command_json(raw)
            for raw in args.feature_gate_command_json
        ]
        report = build_feature_lane_manifest_v0(
            out_dir=args.out_dir,
            profile_path=args.profile,
            genesis_snapshot_path=args.genesis_snapshot,
            tau_app_state_path=args.tau_app_state,
            zusd_state_path=args.zusd_state,
            perp_state_path=args.perp_state,
            oracle_state_path=args.oracle_state,
            oracle_reporter_state_path=args.oracle_reporter_state,
            upba_state_path=args.upba_state,
            proof_mining_state_path=args.proof_mining_state,
            autotrader_state_path=args.autotrader_state,
            confidential_state_path=args.confidential_state,
            tau_chain_balances_path=args.tau_chain_balances,
            tau_chain_id=args.tau_chain_id,
            tau_enable_faucet=bool(args.tau_enable_faucet),
            body_paths=list(args.body),
            module_versions_digest=args.module_versions_digest,
            allow_missing_settlement=bool(args.allow_missing_settlement),
            disable_intent_signatures=bool(args.disable_intent_signatures),
            feature_gate_commands=feature_gate_commands,
        )
    except Exception as exc:
        report = {
            "schema": REPORT_SCHEMA,
            "ok": False,
            "status": "rejected",
            "errors": [str(exc)],
        }
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
