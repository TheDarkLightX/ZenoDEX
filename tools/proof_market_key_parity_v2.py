"""Validate the Python/Rust EconomicWorkKey V2 golden-vector contract."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any, Final

from tools import proof_market_game_theory_v2 as model

REPO_ROOT: Final = Path(__file__).resolve().parents[1]
FIXTURE_PATH: Final = "docs/research/PROOF_MARKET_WORK_KEY_GOLDEN_V2.json"
RECEIPT_PATH: Final = "docs/research/PROOF_MARKET_KEY_PARITY_V2.json"
SOURCE_PATHS: Final = (
    FIXTURE_PATH,
    "tools/check_proof_market_key_parity_v2.py",
    "tools/proof_market_key_parity_v2.py",
    "tools/proof_market_game_theory_economics_v2.py",
    "tools/proof_market_game_theory_v2.py",
    "tools/proof_market_key_parity_rust/Cargo.toml",
    "tools/proof_market_key_parity_rust/Cargo.lock",
    "tools/proof_market_key_parity_rust/src/lib.rs",
    "tools/proof_market_key_parity_rust/tests/golden_vector.rs",
)
SCHEMA: Final = "zenodex/proof-market-work-key-golden/v2"
RECEIPT_SCHEMA: Final = "zenodex/proof-market-key-parity-receipt/v2"
FIELD_ORDER: Final = (
    "product_kind",
    "claim",
    "assumptions",
    "public_inputs",
    "requested_output",
    "verifier_profile",
    "release",
)


def _load_fixture() -> dict[str, Any]:
    value = json.loads((REPO_ROOT / FIXTURE_PATH).read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError("golden vector must contain an object")
    return value


def _load_json(relative_path: str) -> dict[str, Any]:
    value = json.loads((REPO_ROOT / relative_path).read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"{relative_path} must contain an object")
    return value


def _sha256_path(relative_path: str) -> str:
    return hashlib.sha256((REPO_ROOT / relative_path).read_bytes()).hexdigest()


def _strict_descriptor(value: Any) -> model.EconomicWorkDescriptorV2:
    if not isinstance(value, dict) or set(value) != set(FIELD_ORDER):
        raise ValueError("golden descriptor fields are not closed")
    if any(type(value[field]) is not str for field in FIELD_ORDER):
        raise ValueError("golden descriptor values must be exact strings")
    return model.EconomicWorkDescriptorV2(
        product_kind=value["product_kind"],
        claim=value["claim"],
        assumptions=value["assumptions"],
        public_inputs=value["public_inputs"],
        requested_output=value["requested_output"],
        verifier_profile=value["verifier_profile"],
        release=value["release"],
    )


def build_python_evidence() -> dict[str, Any]:
    fixture = _load_fixture()
    descriptor = _strict_descriptor(fixture.get("descriptor"))
    encoding = fixture.get("encoding")
    expected = fixture.get("expected")
    if not isinstance(encoding, dict) or not isinstance(expected, dict):
        raise ValueError("golden vector encoding and expected sections are required")
    framed_bytes = model.canonical_economic_work_key_bytes(descriptor)
    key = model.canonical_economic_work_key(descriptor)
    checks = {
        "SCHEMA_EXACT": fixture.get("schema") == SCHEMA,
        "FIELD_ORDER_EXACT": tuple(encoding.get("field_order", ())) == FIELD_ORDER,
        "DOMAIN_EXACT": encoding.get("domain") == "ZenoDEX/EconomicWorkKey/v2\0",
        "FRAMING_EXACT": (
            encoding.get("length_bytes") == 4
            and encoding.get("length_endian") == "big"
        ),
        "PYTHON_KEY_MATCHES": expected.get("key") == key,
        "PYTHON_BYTES_MATCH": expected.get("framed_bytes_sha256")
        == hashlib.sha256(framed_bytes).hexdigest(),
    }
    return {
        "fixture_path": FIXTURE_PATH,
        "fixture_sha256": hashlib.sha256(
            (REPO_ROOT / FIXTURE_PATH).read_bytes()
        ).hexdigest(),
        "rust_parity_subset": encoding.get("rust_parity_subset"),
        "python_key": key,
        "python_framed_bytes_sha256": hashlib.sha256(framed_bytes).hexdigest(),
        "checks": checks,
        "ok": all(checks.values()),
        "nonclaims": [
            "This validates one ASCII golden vector and does not prove semantic equivalence.",
            "The Rust projection is not a mounted ZenoLedger writer or proof authority.",
            "Unicode NFC runtime parity remains open beyond the declared Rust subset.",
        ],
    }


def build_evidence() -> dict[str, Any]:
    python = build_python_evidence()
    receipt = _load_json(RECEIPT_PATH)
    rows = receipt.get("source_pins")
    source_pin_map = {
        row.get("path"): row.get("sha256")
        for row in rows
        if isinstance(row, dict)
    } if isinstance(rows, list) else {}
    source_pins_match = (
        isinstance(rows, list)
        and len(rows) == len(SOURCE_PATHS)
        and set(source_pin_map) == set(SOURCE_PATHS)
        and all(source_pin_map[path] == _sha256_path(path) for path in SOURCE_PATHS)
    )
    expected_key = python["python_key"]
    expected_bytes_sha256 = python["python_framed_bytes_sha256"]
    python_replay = receipt.get("python_replay")
    rust_replay = receipt.get("rust_replay")
    receipt_checks = {
        "RECEIPT_SCHEMA_EXACT": receipt.get("schema") == RECEIPT_SCHEMA,
        "RECEIPT_STATUS_EXACT": (
            receipt.get("status") == "BOUNDED_CROSS_LANGUAGE_GOLDEN_VECTOR"
        ),
        "RECEIPT_EXTERNAL_AUTH_FALSE": receipt.get("externally_authenticated") is False,
        "RECEIPT_SOURCE_PINS_MATCH": source_pins_match,
        "RECEIPT_FIXTURE_MATCHES": (
            isinstance(receipt.get("fixture"), dict)
            and receipt["fixture"].get("path") == FIXTURE_PATH
            and receipt["fixture"].get("sha256") == python["fixture_sha256"]
            and receipt["fixture"].get("expected_key") == expected_key
            and receipt["fixture"].get("framed_bytes_sha256")
            == expected_bytes_sha256
        ),
        "RECEIPT_PYTHON_REPLAY_MATCHES": (
            isinstance(python_replay, dict)
            and python_replay.get("status") == "PASSED"
            and python_replay.get("command")
            == "python3 tools/check_proof_market_key_parity_v2.py"
            and python_replay.get("key") == expected_key
            and python_replay.get("framed_bytes_sha256") == expected_bytes_sha256
        ),
        "RECEIPT_RUST_REPLAY_MATCHES": (
            isinstance(rust_replay, dict)
            and rust_replay.get("status") == "PASSED"
            and rust_replay.get("command")
            == "cargo test --manifest-path tools/proof_market_key_parity_rust/Cargo.toml --locked"
            and rust_replay.get("passed_tests") == 2
            and rust_replay.get("failed_tests") == 0
            and rust_replay.get("key") == expected_key
            and rust_replay.get("framed_bytes_sha256") == expected_bytes_sha256
        ),
    }
    return {
        "status": "BOUNDED_CROSS_LANGUAGE_GOLDEN_VECTOR",
        "receipt_path": RECEIPT_PATH,
        "receipt_sha256": _sha256_path(RECEIPT_PATH),
        "python": python,
        "rust": rust_replay,
        "receipt_checks": receipt_checks,
        "ok": python["ok"] and all(receipt_checks.values()),
        "nonclaims": [
            "The vector does not prove semantic equivalence between distinct task descriptors.",
            "The Rust projection is not a mounted ZenoLedger writer or proof authority.",
            "Unicode NFC runtime parity remains open beyond the declared Rust subset.",
        ],
    }


def main() -> int:
    evidence = build_evidence()
    print(json.dumps(evidence, indent=2, sort_keys=True))
    return 0 if evidence["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
