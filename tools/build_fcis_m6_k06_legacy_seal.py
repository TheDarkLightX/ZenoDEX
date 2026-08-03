"""Build the source-bound K06 legacy-path seal and checked vector."""

from __future__ import annotations

import json
import sys
from hashlib import sha256
from pathlib import Path
from typing import cast

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.core import fcis_durable_retraction as dra  # noqa: E402
from src.core.fcis_m6_k06_legacy_seal import (  # noqa: E402
    K06FeatureFlagV1,
    K06LegacySealCertificateV1,
    K06LegacySealPolicyV1,
    _mint_legacy_seal_v1,
    feature_flag_root_v1,
    seal_policy_root_v1,
)
from src.state.canonical import canonical_json_bytes  # noqa: E402
from tools.build_fcis_m6_d05_tcg_inventory import (  # noqa: E402
    build_payload as build_d05_payload,
)
from tools.build_fcis_m6_k01_entrypoint_inventory import (  # noqa: E402
    build_payload as build_k01_payload,
)
from tools.check_fcis_m6_k03_static_no_bypass import (  # noqa: E402
    load_policy as load_k03_policy,
)
from tools.check_fcis_m6_k03_static_no_bypass import (  # noqa: E402
    run_static_scan,
)

DEFAULT_CONFIG_PATH = Path("config/deploy/fcis_m6_k06_legacy_seal_v1.json")
DEFAULT_OUTPUT_PATH = Path("docs/research/m6_tasks/TASK_K06_LEGACY_SEAL_V1.json")
K03_POLICY_PATH = Path("config/deploy/fcis_m6_k03_static_no_bypass_policy_v1.json")
K01_CONFIG_PATH = Path("config/deploy/fcis_m6_k01_entrypoint_inventory_v1.json")
J07_VECTOR_PATH = Path("docs/research/m6_tasks/TASK_J07_AUTHORITY_SWITCH_V1.json")


class K06BuildError(ValueError):
    """Raised when an upstream K06 pin or vector is malformed."""


class _DuplicateKey(ValueError):
    pass


def _strict_object(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            raise _DuplicateKey(key)
        result[key] = value
    return result


def _read_json(path: Path) -> dict[str, object]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=_strict_object)
    except (OSError, UnicodeError, json.JSONDecodeError, _DuplicateKey) as exc:
        raise K06BuildError(f"strict JSON load failed for {path}") from exc
    if type(value) is not dict:
        raise K06BuildError(f"JSON root is not an object: {path}")
    return cast(dict[str, object], value)


def _text(value: object, name: str) -> str:
    if type(value) is not str or not value:
        raise K06BuildError(f"{name} must be a nonempty string")
    return value


def _digest(value: object, name: str) -> str:
    checked = _text(value, name)
    if (
        len(checked) != 64
        or checked != checked.lower()
        or any(character not in "0123456789abcdef" for character in checked)
    ):
        raise K06BuildError(f"{name} must be a lowercase digest")
    return checked


def _string_list(value: object, name: str, *, allow_empty: bool = False) -> tuple[str, ...]:
    if type(value) is not list:
        raise K06BuildError(f"{name} must be a JSON array")
    if not allow_empty and not value:
        raise K06BuildError(f"{name} must be nonempty")
    values = tuple(_text(item, f"{name}[{index}]") for index, item in enumerate(value))
    if len(set(values)) != len(values):
        raise K06BuildError(f"{name} contains duplicates")
    if values != tuple(sorted(values, key=lambda item: item.encode("utf-8"))):
        raise K06BuildError(f"{name} is not canonically ordered")
    return values


def _config(path: Path) -> dict[str, object]:
    raw = _read_json(path)
    expected = {
        "schema",
        "profile_id",
        "k03_policy_path",
        "expected_k03_policy_root",
        "expected_k03_scan_root",
        "d05_inventory_root",
        "d05_topology_root",
        "k01_entrypoint_inventory_root",
        "j07_switch_root",
        "j07_post_context_root",
        "j07_post_epoch",
        "target_writer_profile_root",
        "unique_port_id",
        "legacy_symbol_ids",
        "legacy_allowed_paths",
        "sealed_symbol_ids",
        "target_writer_ids",
        "authority_epoch",
        "phase",
        "nonclaims",
    }
    if set(raw) != expected:
        raise K06BuildError("K06 config fields are not exact")
    if raw["schema"] != "zenodex/fcis/m6/k06/legacy-seal-config/v1":
        raise K06BuildError("K06 config schema is wrong")
    _text(raw["profile_id"], "profile_id")
    _text(raw["k03_policy_path"], "k03_policy_path")
    for name in (
        "expected_k03_policy_root",
        "expected_k03_scan_root",
        "d05_inventory_root",
        "d05_topology_root",
        "k01_entrypoint_inventory_root",
        "j07_switch_root",
        "j07_post_context_root",
        "target_writer_profile_root",
    ):
        _digest(raw[name], name)
    _text(raw["unique_port_id"], "unique_port_id")
    for name in (
        "legacy_symbol_ids",
        "legacy_allowed_paths",
        "sealed_symbol_ids",
        "target_writer_ids",
    ):
        _string_list(raw[name], name)
    if type(raw["j07_post_epoch"]) is not int or raw["j07_post_epoch"] < 1:
        raise K06BuildError("j07_post_epoch is not a positive integer")
    if type(raw["authority_epoch"]) is not int or raw["authority_epoch"] < 1:
        raise K06BuildError("authority_epoch is not a positive integer")
    if raw["phase"] != dra.MigrationPhaseV1.LEGACY_DISABLED.value:
        raise K06BuildError("K06 config must seal only at LEGACY_DISABLED")
    nonclaims = raw["nonclaims"]
    if (
        type(nonclaims) is not list
        or not nonclaims
        or any(type(item) is not str or not item for item in nonclaims)
    ):
        raise K06BuildError("nonclaims must be a nonempty string list")
    return raw


def _domain_digest(domain: str, value: object) -> str:
    return sha256(domain.encode("ascii") + b"\x00" + canonical_json_bytes(value)).hexdigest()


def _load_k03_policy_wire(path: Path) -> dict[str, object]:
    return _read_json(path)


def _load_j07(path: Path) -> dict[str, object]:
    value = _read_json(path)
    for name in ("switch_root", "post_context_root", "post_active_profile_root"):
        _digest(value.get(name), f"J07.{name}")
    if value.get("post_phase") != dra.MigrationPhaseV1.AUTHORITY_SWITCH.value:
        raise K06BuildError("J07 post phase is not AUTHORITY_SWITCH")
    if type(value.get("post_epoch_index")) is not int:
        raise K06BuildError("J07 post epoch is not an integer")
    return value


def build_certificate(
    config_path: Path = ROOT / DEFAULT_CONFIG_PATH,
) -> K06LegacySealCertificateV1:
    """Regenerate all current upstream roots before minting the seal."""

    config = _config(config_path.resolve())
    policy_path = (ROOT / _text(config["k03_policy_path"], "k03_policy_path")).resolve()
    try:
        policy_path.relative_to(ROOT)
    except ValueError as exc:
        raise K06BuildError("K03 policy escapes the repository") from exc
    policy_wire = _load_k03_policy_wire(policy_path)
    policy_root = _domain_digest("zenodex/fcis/m6/k06/policy/v1", policy_wire)
    if policy_root != config["expected_k03_policy_root"]:
        raise K06BuildError("K03 policy root differs from K06 pin")
    k03_policy = load_k03_policy(policy_path)
    scan = run_static_scan(ROOT, k03_policy)
    scan_root = _domain_digest("zenodex/fcis/m6/k06/scan/v1", scan)
    if scan_root != config["expected_k03_scan_root"]:
        raise K06BuildError("K03 scan root differs from K06 pin")
    if scan.get("ok") is not True or scan.get("issues") != []:
        raise K06BuildError("K03 source scan failed")

    d05 = build_d05_payload()
    if d05["publisher_inventory_root"] != config["d05_inventory_root"]:
        raise K06BuildError("D05 inventory root differs from K06 pin")
    if d05["topology_root"] != config["d05_topology_root"]:
        raise K06BuildError("D05 topology root differs from K06 pin")
    k01 = build_k01_payload(ROOT / K01_CONFIG_PATH)
    if k01["entrypoint_inventory_root"] != config["k01_entrypoint_inventory_root"]:
        raise K06BuildError("K01 inventory root differs from K06 pin")

    j07 = _load_j07(ROOT / J07_VECTOR_PATH)
    for config_name, j07_name in (
        ("j07_switch_root", "switch_root"),
        ("j07_post_context_root", "post_context_root"),
        ("target_writer_profile_root", "post_active_profile_root"),
    ):
        if j07[j07_name] != config[config_name]:
            raise K06BuildError(f"J07 {j07_name} differs from K06 pin")
    if j07["post_epoch_index"] != config["j07_post_epoch"]:
        raise K06BuildError("J07 post epoch differs from K06 pin")

    legacy_ids = _string_list(config["legacy_symbol_ids"], "legacy_symbol_ids")
    policy_legacy_ids = tuple(
        sorted(k03_policy.legacy_publisher_calls, key=lambda item: item.encode("utf-8"))
    )
    if legacy_ids != policy_legacy_ids:
        raise K06BuildError("K06 legacy symbols differ from K03 policy")
    allowed_paths = _string_list(config["legacy_allowed_paths"], "legacy_allowed_paths")
    policy_allowed_paths = tuple(
        sorted(k03_policy.legacy_allowed_paths, key=lambda item: item.encode("utf-8"))
    )
    if allowed_paths != policy_allowed_paths:
        raise K06BuildError("K06 legacy paths differ from K03 policy")
    sealed_ids = _string_list(config["sealed_symbol_ids"], "sealed_symbol_ids")
    if sealed_ids != legacy_ids:
        raise K06BuildError("K06 sealed symbol set is incomplete")
    target_ids = _string_list(config["target_writer_ids"], "target_writer_ids")
    unique_port_id = _text(config["unique_port_id"], "unique_port_id")
    if unique_port_id not in target_ids:
        raise K06BuildError("K06 target writer set omits the unique port")

    policy = K06LegacySealPolicyV1(
        k03_policy_root=policy_root,
        k03_scan_root=scan_root,
        d05_inventory_root=cast(str, d05["publisher_inventory_root"]),
        d05_topology_root=cast(str, d05["topology_root"]),
        k01_entrypoint_inventory_root=cast(str, k01["entrypoint_inventory_root"]),
        j07_switch_root=cast(str, j07["switch_root"]),
        j07_post_context_root=cast(str, j07["post_context_root"]),
        target_writer_profile_root=cast(str, j07["post_active_profile_root"]),
        unique_port_id=unique_port_id,
        legacy_symbol_ids=legacy_ids,
        legacy_allowed_paths=allowed_paths,
        sealed_symbol_ids=sealed_ids,
        target_writer_ids=target_ids,
    )
    epoch = int(cast(int, config["authority_epoch"]))
    feature_flag = K06FeatureFlagV1(
        flag_id="legacy_publishers_enabled",
        enabled=False,
        authority_epoch=epoch,
        seal_policy_root=seal_policy_root_v1(policy),
        d05_topology_root=policy.d05_topology_root,
        k01_entrypoint_inventory_root=policy.k01_entrypoint_inventory_root,
        target_writer_profile_root=policy.target_writer_profile_root,
    )
    return _mint_legacy_seal_v1(
        policy=policy,
        feature_flag=feature_flag,
        phase=dra.MigrationPhaseV1.LEGACY_DISABLED,
        authority_epoch=epoch,
        sealed_symbol_ids=sealed_ids,
    )


def build_payload(config_path: Path = ROOT / DEFAULT_CONFIG_PATH) -> dict[str, object]:
    """Build the canonical K06 vector and its explicit build-gate summary."""

    certificate = build_certificate(config_path)
    policy_root = seal_policy_root_v1(certificate.policy)
    feature_root = feature_flag_root_v1(certificate.feature_flag)
    return {
        "schema": "zenodex/fcis/m6/k06/legacy-seal-vector/v1",
        "profile_id": "research-unmounted-k06-legacy-seal",
        "seal": certificate.to_wire(),
        "seal_root": certificate.seal_root,
        "policy_root": policy_root,
        "feature_flag_root": feature_root,
        "build_gate": {
            "k03_scan": "PASS",
            "legacy_symbols": "SEALED",
            "legacy_allowed_paths": "SEALED",
            "feature_flag": "DISABLED",
            "phase": dra.MigrationPhaseV1.LEGACY_DISABLED.value,
            "target_writer_set": list(certificate.policy.target_writer_ids),
        },
        "upstream_roots": {
            "k03_policy_root": certificate.policy.k03_policy_root,
            "k03_scan_root": certificate.policy.k03_scan_root,
            "d05_inventory_root": certificate.policy.d05_inventory_root,
            "d05_topology_root": certificate.policy.d05_topology_root,
            "k01_entrypoint_inventory_root": certificate.policy.k01_entrypoint_inventory_root,
            "j07_switch_root": certificate.policy.j07_switch_root,
            "j07_post_context_root": certificate.policy.j07_post_context_root,
            "target_writer_profile_root": certificate.policy.target_writer_profile_root,
        },
    }


def main(argv: list[str] | None = None) -> int:
    args = list(argv or sys.argv[1:])
    config = ROOT / DEFAULT_CONFIG_PATH
    output = ROOT / DEFAULT_OUTPUT_PATH
    check = False
    index = 0
    while index < len(args):
        token = args[index]
        if token == "--check":
            check = True
        elif token == "--config" and index + 1 < len(args):
            index += 1
            candidate = Path(args[index])
            config = candidate if candidate.is_absolute() else ROOT / candidate
        elif token == "--output" and index + 1 < len(args):
            index += 1
            candidate = Path(args[index])
            output = candidate if candidate.is_absolute() else ROOT / candidate
        else:
            raise SystemExit(f"unknown or incomplete argument: {token}")
        index += 1
    payload = build_payload(config)
    encoded = canonical_json_bytes(payload) + b"\n"
    if check:
        if output.read_bytes() != encoded:
            raise SystemExit("FAIL: K06 legacy-seal vector is stale")
    else:
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_bytes(encoded)
    print("K06_LEGACY_SEAL_MATCH", payload["seal_root"])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
