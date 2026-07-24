from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from enum import Enum
from pathlib import Path
from types import SimpleNamespace

import pytest

from tools import run_zrpf_source_opened_spot_v6_durable_admission as runner


def _hash(index: int) -> str:
    return "0x" + f"{index:064x}"


@dataclass(frozen=True)
class _AdmissionCursor:
    revision: int
    state_root: str
    root_count: int
    slot_count: int
    child_claim_count: int
    receipt_count: int
    message_count: int
    chain_id: str | None


@dataclass(frozen=True)
class _SettlementCursor:
    revision: int
    state_root: str
    plan_count: int


class _Disposition(str, Enum):
    COMMITTED = "transaction_committed_authority_false"
    IDEMPOTENT = "idempotent_replay_authority_false"


@dataclass(frozen=True)
class _Result:
    disposition: _Disposition
    admission_head: _AdmissionCursor
    settlement_head: _SettlementCursor
    admission_receipt: object
    settlement_receipt: object
    certificate_receipt: object
    settlement_authority: bool = False

    @property
    def committed(self) -> bool:
        return self.disposition is _Disposition.COMMITTED

    @property
    def idempotent_replay(self) -> bool:
        return self.disposition is _Disposition.IDEMPOTENT


class _FakeStore:
    states: dict[Path, dict[str, object]] = {}
    opens: list[Path] = []

    def __init__(
        self,
        path: Path,
        *,
        genesis_settlement_state_root: str,
        busy_timeout_ms: int = 5_000,
    ) -> None:
        del busy_timeout_ms
        self.path = path
        self.opens.append(path)
        if path not in self.states:
            path.write_bytes(b"fake-sqlite-genesis")
            self.states[path] = {
                "admission": _AdmissionCursor(0, _hash(1), 0, 0, 0, 0, 0, None),
                "settlement": _SettlementCursor(0, genesis_settlement_state_root, 0),
                "committed": False,
            }
        state = self.states[path]
        settlement = state["settlement"]
        assert isinstance(settlement, _SettlementCursor)
        if settlement.revision == 0 and settlement.state_root != genesis_settlement_state_root:
            raise ValueError("genesis state root mismatch")

    @property
    def settlement_authority(self) -> bool:
        return False

    @property
    def authority_blocked_reason(self) -> str:
        return "semantic settlement authority remains disabled"

    def read_admission_cursor(self) -> _AdmissionCursor:
        value = self.states[self.path]["admission"]
        assert isinstance(value, _AdmissionCursor)
        return value

    def read_settlement_cursor(self) -> _SettlementCursor:
        value = self.states[self.path]["settlement"]
        assert isinstance(value, _SettlementCursor)
        return value


class _FakeVerifier:
    calls: list[tuple[Path, bytes, bytes, _AdmissionCursor, _SettlementCursor]] = []
    constructed = 0
    force_first_idempotent = False

    def __init__(
        self,
        *,
        executable: Path,
        authority_manifest_json: bytes,
        authority_manifest_sha256: str,
    ) -> None:
        type(self).constructed += 1
        assert hashlib.sha256(authority_manifest_json).hexdigest() == authority_manifest_sha256
        self.sha256 = hashlib.sha256(executable.read_bytes()).hexdigest()
        self.authority_manifest_sha256 = authority_manifest_sha256

    def verify_and_commit(
        self,
        *,
        store: _FakeStore,
        expected_admission_cursor: _AdmissionCursor,
        expected_settlement_cursor: _SettlementCursor,
        settlement_receipt: bytes,
        guest_input: bytes,
    ) -> _Result:
        self.calls.append(
            (
                store.path,
                settlement_receipt,
                guest_input,
                expected_admission_cursor,
                expected_settlement_cursor,
            )
        )
        state = store.states[store.path]
        assert expected_admission_cursor == state["admission"]
        assert expected_settlement_cursor == state["settlement"]
        already_committed = bool(state["committed"]) or self.force_first_idempotent
        if not already_committed:
            admission = _AdmissionCursor(1, _hash(2), 1, 1, 1, 1, 0, "tau-devnet")
            settlement = _SettlementCursor(1, _hash(3), 1)
            state.update(
                {
                    "admission": admission,
                    "settlement": settlement,
                    "committed": True,
                }
            )
            store.path.write_bytes(b"fake-sqlite-committed")
            disposition = _Disposition.COMMITTED
        else:
            admission = state["admission"]
            settlement = state["settlement"]
            assert isinstance(admission, _AdmissionCursor)
            assert isinstance(settlement, _SettlementCursor)
            disposition = _Disposition.IDEMPOTENT
        admission_receipt = state.setdefault(
            "admission_receipt",
            SimpleNamespace(
                outcome_key=_hash(10),
                root_journal_hash=_hash(11),
                verification_request_sha256=_hash(12)[2:],
            ),
        )
        settlement_receipt_row = state.setdefault(
            "settlement_receipt",
            SimpleNamespace(plan_commitment=_hash(13), root_journal_hash=_hash(11)),
        )
        certificate_receipt = state.setdefault(
            "certificate_receipt",
            SimpleNamespace(
                certificate_journal_hash=_hash(14),
                normalized_plan_commitment=_hash(13),
                settlement_authority=False,
            ),
        )
        return _Result(
            disposition=disposition,
            admission_head=admission,
            settlement_head=settlement,
            admission_receipt=admission_receipt,
            settlement_receipt=settlement_receipt_row,
            certificate_receipt=certificate_receipt,
        )


@pytest.fixture(autouse=True)
def reset_fakes(monkeypatch: pytest.MonkeyPatch) -> None:
    _FakeStore.states = {}
    _FakeStore.opens = []
    _FakeVerifier.calls = []
    _FakeVerifier.constructed = 0
    _FakeVerifier.force_first_idempotent = False
    monkeypatch.setattr(runner, "SQLiteZrpfAtomicSettlementStoreV1", _FakeStore)
    monkeypatch.setattr(runner, "PinnedSourceOpenedSpotSettlementVerifierV6", _FakeVerifier)


def _inputs(tmp_path: Path) -> dict[str, Path]:
    verifier = tmp_path / "verifier"
    verifier.write_bytes(b"static-verifier")
    verifier.chmod(0o700)
    manifest = tmp_path / "manifest.json"
    manifest.write_bytes(b'{"schema":"test-manifest"}')
    receipt = tmp_path / "settlement.receipt.json"
    receipt.write_bytes(b'{"receipt":"succinct"}')
    guest_input = tmp_path / "settlement.input.bin"
    guest_input.write_bytes(b"exact-guest-input")
    return {
        "verifier": verifier,
        "manifest": manifest,
        "receipt": receipt,
        "guest_input": guest_input,
        "database": tmp_path / "admission.sqlite3",
        "output": tmp_path / "admission-evidence.json",
    }


def _run(
    paths: dict[str, Path],
    *,
    expected_manifest_sha256: str | None = None,
) -> tuple[dict[str, object], bytes]:
    expected = (
        expected_manifest_sha256 or hashlib.sha256(paths["manifest"].read_bytes()).hexdigest()
    )
    return runner.run_durable_admission_evidence(
        verifier_path=paths["verifier"],
        authority_manifest_path=paths["manifest"],
        settlement_receipt_path=paths["receipt"],
        guest_input_path=paths["guest_input"],
        database_path=paths["database"],
        output_path=paths["output"],
        expected_authority_manifest_sha256=expected,
        genesis_settlement_state_root=_hash(1),
    )


def test_runner_commits_reopens_and_proves_exact_retry_idempotence(
    tmp_path: Path,
) -> None:
    paths = _inputs(tmp_path)

    report, raw = _run(paths)

    assert report["ok"] is True
    assert report["settlement_authority"] is False
    assert report["release_authority"] is False
    assert report["production_authority"] is False
    assert report["genesis_settlement_state_root"] == _hash(1)
    assert report["first_commit"]["committed"] is True  # type: ignore[index]
    assert report["exact_retry"]["idempotent_replay"] is True  # type: ignore[index]
    assert report["reopen_count"] == 2
    assert len(_FakeStore.opens) == 3
    assert _FakeVerifier.constructed == 1
    assert len(_FakeVerifier.calls) == 2
    assert _FakeVerifier.calls[0][1:3] == _FakeVerifier.calls[1][1:3]
    assert paths["output"].read_bytes() == raw
    assert raw.endswith(b"\n")
    assert (
        json.dumps(json.loads(raw), sort_keys=True, separators=(",", ":")).encode() + b"\n" == raw
    )


def test_runner_rejects_a_noncommitting_first_attempt(tmp_path: Path) -> None:
    paths = _inputs(tmp_path)
    _FakeVerifier.force_first_idempotent = True

    with pytest.raises(
        runner.DurableAdmissionEvidenceError,
        match="first admission did not commit",
    ):
        _run(paths)

    assert not paths["output"].exists()


@pytest.mark.parametrize("occupied", ("database", "output"))
def test_runner_rejects_preexisting_output_state(
    tmp_path: Path,
    occupied: str,
) -> None:
    paths = _inputs(tmp_path)
    paths[occupied].write_bytes(b"preexisting")

    with pytest.raises(runner.DurableAdmissionEvidenceError, match="must not already exist"):
        _run(paths)

    assert _FakeVerifier.constructed == 0
    assert _FakeVerifier.calls == []


def test_runner_rejects_symlinked_receipt_before_verification(tmp_path: Path) -> None:
    paths = _inputs(tmp_path)
    target = paths["receipt"]
    link = tmp_path / "linked-receipt.json"
    link.symlink_to(target)
    paths["receipt"] = link

    with pytest.raises(runner.DurableAdmissionEvidenceError, match="symlink"):
        _run(paths)

    assert _FakeVerifier.calls == []


def test_runner_rejects_self_consistent_ungoverned_manifest(
    tmp_path: Path,
) -> None:
    paths = _inputs(tmp_path)
    governed_manifest_sha256 = hashlib.sha256(paths["manifest"].read_bytes()).hexdigest()
    paths["manifest"].write_bytes(b'{"schema":"attacker-selected-manifest"}')
    paths["verifier"].write_bytes(b"matching-attacker-selected-verifier")

    with pytest.raises(
        runner.DurableAdmissionEvidenceError,
        match="does not match the governed expected digest",
    ):
        _run(paths, expected_manifest_sha256=governed_manifest_sha256)

    assert _FakeVerifier.constructed == 0
    assert _FakeVerifier.calls == []
    assert not paths["database"].exists()
    assert not paths["output"].exists()


def test_cli_failure_emits_canonical_non_authority_report(
    tmp_path: Path,
    capsys: pytest.CaptureFixture[str],
) -> None:
    paths = _inputs(tmp_path)
    paths["database"].write_bytes(b"occupied")

    exit_code = runner.main(
        [
            "--verifier",
            str(paths["verifier"]),
            "--authority-manifest",
            str(paths["manifest"]),
            "--settlement-receipt",
            str(paths["receipt"]),
            "--guest-input",
            str(paths["guest_input"]),
            "--database",
            str(paths["database"]),
            "--output",
            str(paths["output"]),
            "--expected-authority-manifest-sha256",
            hashlib.sha256(paths["manifest"].read_bytes()).hexdigest(),
            "--genesis-settlement-state-root",
            _hash(1),
        ]
    )

    assert exit_code == 1
    stdout = capsys.readouterr().out.encode()
    assert paths["output"].read_bytes() == stdout
    failure = json.loads(stdout)
    assert failure == {
        "error_code": "fresh_path_required",
        "ok": False,
        "production_authority": False,
        "release_authority": False,
        "schema": runner.ERROR_SCHEMA,
        "settlement_authority": False,
    }


def test_report_encoder_rejects_oversized_output() -> None:
    with pytest.raises(runner.DurableAdmissionEvidenceError, match="report exceeds"):
        runner._canonical_report_bytes({"oversized": "x" * runner.MAX_REPORT_BYTES})
