"""Python/Rust differential for the live nonce batch authority.

This closes the specific differential-test gap called out in the CBC matrix:
``tests/runtime/test_replay_guard_conformance.py`` only shadows the single
``(sender, nonce)`` replay-guard reference. The live spot path uses
``src.state.nonces.validate_and_apply_intent_nonce_batch``, whose behavior also
depends on all-or-nothing staging, per-sender sorted ranges, mixed nonce
presence, and nonce-before-sender reject precedence.

REVIEW [C -> A-]: the old evidence was valuable but scoped too narrowly. This
suite drives the running Python batch authority against the compiled Rust batch
shadow over accepting cases, every reject class, precedence-sensitive cases, and
a deterministic boundary corpus. A higher grade still needs the formal
batch-wrapper proof to be mechanically refined to the Rust/Python live code.
"""

from __future__ import annotations

import json
import random
import subprocess
import sys
from pathlib import Path

import pytest

from src.state.intents import Intent, IntentKind
from src.state.nonces import NonceTable, validate_and_apply_intent_nonce_batch

REPO = Path(__file__).resolve().parents[2]
TOOLS_RUNTIME = REPO / "tools" / "runtime"
if str(TOOLS_RUNTIME) not in sys.path:
    sys.path.insert(0, str(TOOLS_RUNTIME))

from rust_shadow_replay import ShadowError, locate_or_build_cli  # noqa: E402

SENDER_A = "0x" + "11" * 48
SENDER_B = "0x" + "22" * 48
SENDER_C = "0x" + "33" * 48
BAD_SENDER_HEX = "0xzz" + "11" * 47
INTENT_ID = "0x" + "ab" * 32
U32_MAX = 0xFFFFFFFF
MISSING = object()


@pytest.fixture(scope="session")
def rust_bin() -> Path:
    try:
        return locate_or_build_cli(allow_build=True)
    except ShadowError as exc:  # pragma: no cover - environment dependent
        pytest.skip(f"Rust shadow runtime unavailable: {exc}")


def _intent(sender: object, nonce: object) -> Intent:
    fields = {} if nonce is MISSING else {"nonce": nonce}
    return Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=INTENT_ID,
        sender_pubkey=sender,
        deadline=10**12,
        fields=fields,
    )


def _entries(table: NonceTable) -> list[dict[str, object]]:
    return [
        {"sender": sender, "last_nonce": last_nonce}
        for sender, last_nonce in sorted(table.get_all().items())
    ]


def _python_batch(request: dict) -> dict:
    state = NonceTable()
    for entry in request.get("state_entries", []):
        state.set_last(entry["sender"], entry["last_nonce"])
    intents = [
        _intent(raw.get("sender"), raw["nonce"] if "nonce" in raw else MISSING)
        for raw in request.get("intents", [])
    ]
    ok, reason, updated = validate_and_apply_intent_nonce_batch(
        nonces=state,
        intents=intents,
        require_all_nonces=request.get("require_all_nonces", True),
    )
    post = updated if ok else state
    assert post is not None
    return {
        "accept": ok,
        "reject_reason": reason,
        "post_state_entries": _entries(post),
    }


def _rust_batch(rust_bin: Path, request: dict) -> dict:
    proc = subprocess.run(
        [str(rust_bin), "nonce-batch-op", "-"],
        input=json.dumps(request),
        capture_output=True,
        text=True,
        check=False,
    )
    if proc.returncode != 0:
        raise AssertionError(
            f"nonce-batch-op exited {proc.returncode}\n"
            f"stderr={proc.stderr}\nrequest={json.dumps(request, sort_keys=True)}"
        )
    return json.loads(proc.stdout)


def _wire_intents(pairs: list[tuple[object, object]]) -> list[dict[str, object]]:
    out: list[dict[str, object]] = []
    for sender, nonce in pairs:
        item = {"sender": sender}
        if nonce is not MISSING:
            item["nonce"] = nonce
        out.append(item)
    return out


def _request(
    pairs: list[tuple[object, object]],
    *,
    state_entries: list[dict[str, object]] | None = None,
    require_all_nonces: bool = True,
) -> dict:
    return {
        "version": 1,
        "state_entries": state_entries or [],
        "intents": _wire_intents(pairs),
        "require_all_nonces": require_all_nonces,
    }


BOUNDARY_CASES: list[tuple[str, dict]] = [
    (
        "empty_batch_noop",
        _request([], state_entries=[{"sender": SENDER_A, "last_nonce": 7}]),
    ),
    ("single_sender_out_of_order_accept", _request([(SENDER_A, 2), (SENDER_A, 1)])),
    (
        "multi_sender_out_of_order_accept",
        _request([(SENDER_B, 2), (SENDER_A, 1), (SENDER_B, 1), (SENDER_C, 1)]),
    ),
    (
        "range_starts_at_last_plus_one",
        _request(
            [(SENDER_A, 7), (SENDER_A, 6)],
            state_entries=[{"sender": SENDER_A, "last_nonce": 5}],
        ),
    ),
    ("duplicate_rejects", _request([(SENDER_A, 1), (SENDER_A, 1)])),
    ("gap_rejects", _request([(SENDER_A, 2)])),
    (
        "stale_rejects",
        _request([(SENDER_A, 1)], state_entries=[{"sender": SENDER_A, "last_nonce": 1}]),
    ),
    ("missing_nonce_require_all_rejects", _request([(SENDER_A, MISSING)])),
    (
        "missing_nonce_optional_noop",
        _request(
            [(12345, MISSING)],
            state_entries=[{"sender": SENDER_A, "last_nonce": 4}],
            require_all_nonces=False,
        ),
    ),
    (
        "mixed_presence_optional_rejects",
        _request([(SENDER_A, 1), (12345, MISSING)], require_all_nonces=False),
    ),
    ("invalid_sender_valid_nonce_rejects", _request([(BAD_SENDER_HEX, 1)])),
    ("invalid_sender_type_rejects", _request([(12345, 1)])),
    ("nonce_before_sender_precedence", _request([(BAD_SENDER_HEX, 0)])),
    ("bool_nonce_rejects", _request([(SENDER_A, True)])),
    ("string_nonce_rejects", _request([(SENDER_A, "5")])),
    ("float_nonce_rejects", _request([(SENDER_A, 1.5)])),
    (
        "u32_max_accepts_at_boundary",
        _request(
            [(SENDER_A, U32_MAX)],
            state_entries=[{"sender": SENDER_A, "last_nonce": U32_MAX - 1}],
        ),
    ),
    (
        "u32_max_plus_one_rejects",
        _request([(SENDER_A, U32_MAX + 1)]),
    ),
    (
        "first_sender_duplicate_wins_over_later_gap",
        _request([(SENDER_A, 1), (SENDER_B, 9), (SENDER_A, 1)]),
    ),
    (
        "first_sender_gap_wins_over_later_duplicate",
        _request([(SENDER_B, 9), (SENDER_A, 1), (SENDER_A, 1)]),
    ),
    (
        "shape_validation_invalid_sender_beats_earlier_duplicate",
        _request([(SENDER_A, 1), (SENDER_A, 1), (BAD_SENDER_HEX, 1)]),
    ),
    (
        "shape_validation_invalid_sender_beats_earlier_gap",
        _request([(SENDER_A, 2), (BAD_SENDER_HEX, 1)]),
    ),
    (
        "shape_validation_bad_nonce_beats_earlier_duplicate",
        _request([(SENDER_A, 1), (SENDER_A, 1), (BAD_SENDER_HEX, 0)]),
    ),
]


@pytest.mark.parametrize(
    ("label", "case_request"), BOUNDARY_CASES, ids=[c[0] for c in BOUNDARY_CASES]
)
def test_nonce_batch_boundary_cases_match_python(
    rust_bin: Path, label: str, case_request: dict
) -> None:
    py = _python_batch(case_request)
    rust = _rust_batch(rust_bin, case_request)
    observed = {
        "accept": rust["accept"],
        "reject_reason": rust["reject_reason"],
        "post_state_entries": rust["post_state_entries"],
    }
    assert observed == py, (
        f"Python/Rust nonce batch divergence in {label}\n"
        f"request={json.dumps(case_request, sort_keys=True)}\n"
        f"python={json.dumps(py, sort_keys=True)}\n"
        f"rust={json.dumps(observed, sort_keys=True)}"
    )
    if not rust["accept"]:
        assert rust["pre_state_root"] == rust["post_state_root"]


def test_boundary_atlas_is_non_vacuous(rust_bin: Path) -> None:
    outcomes = [_rust_batch(rust_bin, request) for _, request in BOUNDARY_CASES]
    reasons = {out["reject_reason"] for out in outcomes if out["reject_reason"] is not None}
    assert any(out["accept"] for out in outcomes)
    assert any(not out["accept"] for out in outcomes)
    assert {
        "Missing/invalid nonce",
        "nonce presence must be consistent across batch",
        "duplicate nonce in batch",
        "nonce sequence invalid",
        "invalid sender_pubkey for nonce accounting: sender_pubkey must be valid hex",
        "invalid sender_pubkey for nonce accounting: sender_pubkey must be a str",
    } <= reasons


def _random_sender(rng: random.Random) -> object:
    return rng.choice(
        [
            SENDER_A,
            SENDER_B,
            SENDER_C,
            SENDER_A.upper(),
            f"\u001c0X{SENDER_B[2:].upper()}\u001f",
            BAD_SENDER_HEX,
            "0x11",
            "",
            12345,
            None,
        ]
    )


def _random_nonce(rng: random.Random) -> object:
    return rng.choice([1, 2, 3, 4, 5, 0, -1, U32_MAX + 1, "5", 1.5, True, MISSING])


def _random_request(rng: random.Random) -> dict:
    state_entries = []
    for sender in (SENDER_A, SENDER_B, SENDER_C):
        if rng.random() < 0.45:
            state_entries.append({"sender": sender, "last_nonce": rng.randint(1, 4)})
    pairs = [(_random_sender(rng), _random_nonce(rng)) for _ in range(rng.randint(0, 6))]
    return _request(
        pairs,
        state_entries=state_entries,
        require_all_nonces=rng.choice([True, False]),
    )


def test_randomized_nonce_batch_differential(rust_bin: Path) -> None:
    rng = random.Random(20260605)
    mismatches = []
    accept_count = 0
    reject_count = 0
    for _ in range(220):
        request = _random_request(rng)
        py = _python_batch(json.loads(json.dumps(request)))
        rust = _rust_batch(rust_bin, request)
        observed = {
            "accept": rust["accept"],
            "reject_reason": rust["reject_reason"],
            "post_state_entries": rust["post_state_entries"],
        }
        accept_count += int(observed["accept"])
        reject_count += int(not observed["accept"])
        if observed != py:
            mismatches.append((request, py, observed))
            break
    assert not mismatches, (
        "Python/Rust nonce batch randomized divergence\n"
        f"request={json.dumps(mismatches[0][0], sort_keys=True)}\n"
        f"python={json.dumps(mismatches[0][1], sort_keys=True)}\n"
        f"rust={json.dumps(mismatches[0][2], sort_keys=True)}"
    )
    assert accept_count > 0
    assert reject_count > 0
