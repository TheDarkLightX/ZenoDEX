"""Native replay of the candidate guest input, using independent Python roots.

No zkVM build, real proof, verifier acceptance or publication is claimed here.
"""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import tempfile
from copy import deepcopy
from dataclasses import replace
from pathlib import Path

import pytest

from src.core.global_economic_state_ownership_v2 import ReplayStateV2
from src.core.global_settlement_types_v2 import canonical_global_bytes_v2
from tests.core.test_spot_swap_global_rust_v2 import (
    _balance_capacity_cases,
    _byte_capacity_cases,
    _capacity_cases,
    _case,
    _economic_cases,
    _guard_cases,
    _history_cases,
    _intent_boundary_cases,
    _require_python_input_rejection,
    _reserve_boundary_cases,
)
from tests.core.test_spot_swap_global_v2 import command, initial

ROOT = Path(__file__).resolve().parents[2]
MANIFEST = ROOT / "zk/spot_swap_global_risc0/Cargo.toml"
KEYS = ("assets", "spot", "state", "intent", "occurrence", "block_timestamp")


@pytest.fixture(scope="module")
def spot_frame_replay():
    target = Path(os.environ.get("ZENODEX_SPOT_GUEST_NATIVE_TARGET",
                                 "/dev/shm/zenodex-spot-guest-native-20260914"))
    if shutil.disk_usage(target if target.exists() else target.parent).free < 4 * 1024**3:
        pytest.skip("four GiB required for native guest harness; no guest qualification")
    result = subprocess.run(
        ["cargo", "+1.90.0", "build", "--offline", "--locked", "--manifest-path", str(MANIFEST),
         "--examples", "--bins", "-j", "2"], cwd=ROOT, capture_output=True, text=True, timeout=180,
        env={**os.environ, "CARGO_TARGET_DIR": str(target)}, check=False,
    )
    assert result.returncode == 0, result.stderr
    assert sum(p.stat().st_size for p in target.rglob("*") if p.is_file()) < 1024**3
    return target / "debug/examples/replay"


def _frame(wire, *, components=None):
    parts = [canonical_global_bytes_v2(wire[key]) for key in KEYS] if components is None else components
    frame = b"ZDSS2\0" + b"".join(len(part).to_bytes(4, "little") + part for part in parts)
    return len(frame).to_bytes(4, "little") + frame


def _run(binary, frame):
    return subprocess.run([str(binary)], input=frame, capture_output=True, timeout=30, check=False)


@pytest.fixture(scope="module")
def positive_case():
    return _economic_cases()[0]


@pytest.mark.parametrize("make_cases", [
    _economic_cases, _guard_cases, _history_cases, _capacity_cases,
    _balance_capacity_cases, _byte_capacity_cases, _reserve_boundary_cases, _intent_boundary_cases,
])
def test_shared_execution_matches_python_acceptance_and_committed_roots(spot_frame_replay, make_cases):
    for label, wire, expected in make_cases():
        result = _run(spot_frame_replay, _frame(wire))
        if expected["status"] == "accepted":
            journal = canonical_global_bytes_v2({
                "schema": "zenodex/spot-swap-global-statement/v2",
                "input_root": expected["statement_root"],
                "refinement_root": expected["refinement_root"],
            })
            assert (result.returncode, result.stdout) == (0, journal), (label, result.stderr)
        else:
            assert result.returncode == 2 and result.stdout == b"", (label, result)
            assert expected["code"] in result.stderr.decode(), (label, result.stderr)


@pytest.mark.parametrize("defect", ["duplicate", "escaped_duplicate", "private_number", "missing_salt",
                                     "timestamp_bool", "timestamp_float", "unknown_field", "whitespace"])
def test_canonical_frame_rejects_aliases_without_emitting_journal(spot_frame_replay, positive_case, defect):
    _, wire, expected = positive_case
    parts = [canonical_global_bytes_v2(wire[key]) for key in KEYS]
    intent = deepcopy(wire["intent"])
    if defect in ("duplicate", "escaped_duplicate"):
        name = b'"deadline"' if defect == "duplicate" else b'"deadlin\\u0065"'
        parts[3] = parts[3][:-1] + b"," + name + b":" + str(intent["deadline"]).encode() + b"}"
    elif defect == "private_number":
        key = "amount_in" if "amount_in" in intent["fields"] else "amount_out"
        intent["fields"][key] = {"$serde_json::private::Number": str(intent["fields"][key])}
        # Python's encoder preserves the object; the native decoder must not
        # turn it into an integer before comparing against the original bytes.
        parts[3] = json.dumps(intent, sort_keys=True, separators=(",", ":")).encode()
    elif defect == "missing_salt":
        del intent["salt"]
        parts[3] = canonical_global_bytes_v2(intent)
    elif defect == "unknown_field":
        intent["verified"] = True
        parts[3] = json.dumps(intent, sort_keys=True, separators=(",", ":")).encode()
    elif defect == "whitespace":
        parts[0] += b" "
    else:
        parts[5] = b"true" if defect == "timestamp_bool" else b"100.0"
    result = _run(spot_frame_replay, _frame(wire, components=parts))
    assert result.returncode == 2 and result.stdout == b"", result
    assert b"Component(" in result.stderr
    positive = _run(spot_frame_replay, _frame(wire))
    assert positive.returncode == 0, positive.stderr
    assert json.loads(positive.stdout)["input_root"] == expected["statement_root"]


def test_outer_transport_refuses_truncation_and_extension_before_journal(spot_frame_replay, positive_case):
    _, wire, _ = positive_case
    frame = _frame(wire)
    for bad in [b"", frame[:3], frame[:-1], frame + b"x", (2**32 - 1).to_bytes(4, "little")]:
        result = _run(spot_frame_replay, bad)
        assert result.returncode == 2 and result.stdout == b"", result
    assert _run(spot_frame_replay, frame).returncode == 0


@pytest.mark.parametrize("defect", ["nested-nonce", "boolean-nonce", "lp-coverage"])
def test_structurally_invalid_values_cannot_emit_a_journal(spot_frame_replay, defect):
    inputs = initial()
    cases = []
    _case(cases, "positive", inputs, command(inputs[1]))
    wire = deepcopy(cases[0][1])
    if defect == "lp-coverage":
        wire["spot"]["lp_positions"][1]["shares"] += 1
    else:
        wire["intent"]["fields"]["nonce"] = [] if defect == "nested-nonce" else True
    _require_python_input_rejection(defect, inputs, wire)
    result = _run(spot_frame_replay, _frame(wire))
    assert (result.returncode, result.stdout) == (2, b"")
    reason = (
        b'Transition(SpotState(InvalidBinding("Spot LP ownership must cover the complete supply")))'
        if defect == "lp-coverage"
        else b'Transition(Intent(InvalidBinding("swap intent fields must contain exact flat scalars")))'
    )
    assert result.stderr == b"Spot execution frame rejected: " + reason + b"\n"
    assert _run(spot_frame_replay, _frame(cases[0][1])).returncode == 0


def test_native_guest_binary_cannot_impersonate_zkvm_execution(spot_frame_replay, positive_case):
    binary = spot_frame_replay.parents[1] / "zenodex-spot-swap-global-guest"
    result = _run(binary, _frame(positive_case[1]))
    assert (result.returncode, result.stdout) == (2, b"")


def test_transport_refuses_an_economically_valid_successor_over_its_byte_ceiling(spot_frame_replay):
    # Given a complete global state at the transport ceiling, adding one replay
    # row is economically valid but cannot yield another representable frame.
    assets, spot, state = initial()
    ceiling = 1024**2
    row = ReplayStateV2("retained-00000000", "0x" + "1" * 64)
    row_size = len(canonical_global_bytes_v2(row)) + 1
    count = (ceiling - len(canonical_global_bytes_v2(state)) + 1) // row_size
    rows = tuple(ReplayStateV2(f"retained-{i:08}", f"0x{i + 1:064x}") for i in range(count))
    full = replace(state, replay_state=rows)
    padding = ceiling - len(canonical_global_bytes_v2(full))
    padded_row = replace(rows[-1], replay_id=rows[-1].replay_id + "x" * padding)
    full = replace(full, replay_state=(*rows[:-1], padded_row))
    assert len(canonical_global_bytes_v2(full)) == ceiling
    cases = []
    _case(cases, "fits-after-insertion", (assets, spot, replace(state, replay_state=rows[:-2])), command(spot))
    _case(cases, "successor-exceeds-frame", (assets, spot, full), command(spot))
    for label, wire, expected in cases:
        assert expected["status"] == "accepted"
        result = _run(spot_frame_replay, _frame(wire))
        if label == "fits-after-insertion":
            assert len(canonical_global_bytes_v2(expected["post_state"])) <= ceiling
            assert result.returncode == 0, result.stderr
            assert json.loads(result.stdout)["refinement_root"] == expected["refinement_root"]
        else:
            assert len(canonical_global_bytes_v2(expected["post_state"])) > ceiling
            assert (result.returncode, result.stdout) == (2, b"")
            assert b"SuccessorBounds" in result.stderr


@pytest.fixture(scope="module")
def frame_mutant_target(spot_frame_replay):
    with tempfile.TemporaryDirectory(prefix="frame-mutants-", dir=spot_frame_replay.parents[2]) as target:
        yield target


@pytest.mark.parametrize("defect", ["original_bytes", "input_root"])
def test_compiled_frame_mutants_change_the_protected_observation(
    spot_frame_replay, positive_case, frame_mutant_target, tmp_path, defect,
):
    _, wire, expected = positive_case
    positive = _run(spot_frame_replay, _frame(wire))
    assert positive.returncode == 0
    assert json.loads(positive.stdout)["input_root"] == expected["statement_root"]
    payload = _frame(wire)
    if defect == "original_bytes":
        parts = [canonical_global_bytes_v2(wire[key]) for key in KEYS]
        parts[0] += b" "
        payload = _frame(wire, components=parts)
        control = _run(spot_frame_replay, payload)
        assert control.returncode == 2 and control.stdout == b"" and b"Component(" in control.stderr
    core = tmp_path / "spot_swap_global_v2"
    guest = tmp_path / "spot_swap_global_risc0"
    shutil.copytree(ROOT / "zk/spot_swap_global_v2", core, ignore=shutil.ignore_patterns("target"))
    shutil.copytree(MANIFEST.parent, guest, ignore=shutil.ignore_patterns("target"))
    manifest = core / "Cargo.toml"
    manifest.write_text(manifest.read_text().replace(
        '../global_settlement_abi_v2', str(ROOT / 'zk/global_settlement_abi_v2')))
    source = core / "src/frame.rs"
    old = "if canonical_bytes_v2(&value).map_err(|_| error())? != bytes {" if defect == "original_bytes" else "input_root: accepted.statement_root(),"
    new = "if false && canonical_bytes_v2(&value).map_err(|_| error())? != bytes {" if defect == "original_bytes" else "input_root: &refinement_root,"
    text = source.read_text()
    assert text.count(old) == 1
    source.write_text(text.replace(old, new))
    build = subprocess.run(
        ["cargo", "+1.90.0", "build", "--offline", "--locked", "--manifest-path", str(guest / "Cargo.toml"),
         "--examples", "-j", "2"], capture_output=True, text=True, timeout=180, check=False,
        env={**os.environ, "CARGO_TARGET_DIR": frame_mutant_target, "CARGO_INCREMENTAL": "0"},
    )
    assert build.returncode == 0, build.stderr  # A compiler failure is never a mutant kill.
    changed = _run(Path(frame_mutant_target) / "debug/examples/replay", payload)
    assert changed.returncode == 0, changed.stderr
    if defect == "original_bytes":
        assert changed.stdout == positive.stdout  # The malformed frame was incorrectly accepted.
    else:
        assert json.loads(changed.stdout)["input_root"] == expected["refinement_root"]
        assert changed.stdout != positive.stdout  # The independent Python input-root oracle detects it.
