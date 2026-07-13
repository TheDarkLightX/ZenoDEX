from __future__ import annotations

import hashlib
import json
import multiprocessing
import os
import stat
import textwrap
import time
from dataclasses import replace
from multiprocessing.connection import Connection
from pathlib import Path

import pytest

from tools import run_zrpf_source_opened_spot_v6_proof_chain as runner

IMAGE_IDS = {
    "leaf": "11" * 32,
    "level_one": "22" * 32,
    "level_two": "33" * 32,
    "settlement": "44" * 32,
}

PROGRAM_NAMES = {
    "leaf": "spot_value_leaf_v6.bin",
    "level_one": "spot_value_aggregate_l1_v6.bin",
    "level_two": "spot_value_aggregate_l2_v6.bin",
    "settlement": "source_opened_spot_settlement_v6.bin",
}


def test_receipt_profile_matches_the_governed_verifier_contract() -> None:
    assert (
        runner.SUCCINCT_PROFILE_ID
        == "risc0_succinct_poseidon2_resolve_3_0_5_v1"
    )


def _sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _compact(value: object) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode()


def _receipt(role: str) -> bytes:
    return _compact(
        {
            "inner": {
                "Succinct": {
                    "claim": {"role": role},
                    "control_id": [1, 2, 3, 4],
                    "control_inclusion_proof": [],
                    "hashfn": "poseidon2",
                    "seal": [7, 8, 9, 10],
                    "verifier_parameters": [11, 12, 13, 14],
                }
            },
            "journal": {"bytes": [len(role), 6, 7]},
            "metadata": {"verifier_parameters": [11, 12, 13, 14]},
        }
    )


def _mutate_receipt(raw: bytes) -> bytes:
    value = json.loads(raw)
    value["inner"]["Succinct"]["seal"][1] ^= 1
    return _compact(value)


def _write_executable(path: Path, source: str) -> None:
    path.write_text("#!/usr/bin/python3\n" + source, encoding="utf-8")
    path.chmod(0o700)


def _r0vm_source(image_ids: dict[str, str], *, wrong_role: str | None = None) -> str:
    mapping = {
        PROGRAM_NAMES[role]: (
            "ff" * 32 if role == wrong_role else image_ids[role]
        )
        for role in PROGRAM_NAMES
    }
    return textwrap.dedent(
        f"""
        import pathlib
        import sys

        mapping = {mapping!r}
        if len(sys.argv) != 4 or sys.argv[1] != "--elf" or sys.argv[3] != "--id":
            raise SystemExit(9)
        name = pathlib.Path(sys.argv[2]).name
        if name not in mapping:
            raise SystemExit(8)
        print(mapping[name])
        """
    )


def _prover_source(
    role: str,
    *,
    program_sha256: str,
    image_id: str,
    fault: str | None = None,
    escaped_child: Path | None = None,
) -> str:
    return textwrap.dedent(
        f"""
        import hashlib
        import json
        import os
        import pathlib
        import subprocess
        import sys
        import time

        role = {role!r}
        fault = {fault!r}
        image_id = {image_id!r}
        program_sha256 = {program_sha256!r}
        escaped_child = {str(escaped_child) if escaped_child is not None else None!r}
        required_environment = {{
            "HOME", "LANG", "LC_ALL", "PATH", "RISC0_SERVER_PATH",
            "RISC0_PROVER", "TMPDIR", "TZ",
        }}
        if set(os.environ) != required_environment:
            print("environment mismatch", file=sys.stderr)
            raise SystemExit(31)
        if "RISC0_DEV_MODE" in os.environ:
            raise SystemExit(32)
        if os.environ["RISC0_PROVER"] != "ipc":
            raise SystemExit(36)
        tmpdir = pathlib.Path(os.environ["TMPDIR"])
        if tmpdir.stat().st_mode & 0o777 != 0o700:
            raise SystemExit(33)
        if not pathlib.Path(os.environ["RISC0_SERVER_PATH"]).exists():
            raise SystemExit(34)

        if fault == "nonzero":
            print("governed fake failure", file=sys.stderr)
            raise SystemExit(7)
        if fault == "stdout_overflow":
            sys.stdout.write("x" * 200000)
            sys.stdout.flush()
            time.sleep(60)
        if fault == "timeout":
            subprocess.Popen([
                "/usr/bin/python3", "-c",
                "import pathlib,time;time.sleep(1.5);pathlib.Path(" + repr(escaped_child) + ").write_text('escaped')",
            ])
            time.sleep(60)
        if fault == "residual_child":
            subprocess.Popen(
                [
                    "/usr/bin/python3", "-c",
                    "import pathlib,time;time.sleep(1.5);pathlib.Path(" + repr(escaped_child) + ").write_text('escaped')",
                ],
                stdin=subprocess.DEVNULL,
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
            )

        args = sys.argv[1:]
        if len(args) % 2:
            raise SystemExit(35)
        options = dict(zip(args[0::2], args[1::2], strict=True))

        def digest(path):
            return hashlib.sha256(pathlib.Path(path).read_bytes()).hexdigest()

        def write(path, raw):
            pathlib.Path(path).write_bytes(raw)

        def compact(value):
            return json.dumps(value, sort_keys=True, separators=(",", ":")).encode()

        def receipt(name):
            return compact({{
                "inner": {{"Succinct": {{
                    "claim": {{"role": name}},
                    "control_id": [1, 2, 3, 4],
                    "control_inclusion_proof": [],
                    "hashfn": "poseidon2",
                    "seal": [7, 8, 9, 10],
                    "verifier_parameters": [11, 12, 13, 14],
                }}}},
                "journal": {{"bytes": [len(name), 6, 7]}},
                "metadata": {{"verifier_parameters": [11, 12, 13, 14]}},
            }})

        raw = receipt(role)
        if role == "leaf":
            envelope = b"source-opened-leaf-envelope-v6"
            if fault == "fifo_output":
                os.mkfifo(options["--receipt-out"], 0o600)
            else:
                write(options["--receipt-out"], raw)
            write(options["--source-envelope-out"], envelope)
            if fault == "extra_output":
                pathlib.Path(options["--receipt-out"]).with_name("unexpected").write_bytes(b"x")
            report = {{
                "action_nullifier_root": "55" * 32,
                "adapter_receipt_sha256": digest(options["--adapter-receipt"]),
                "candidate_accepted": True,
                "guest_program_binary_bytes": {4 + len('leaf-program')},
                "guest_program_binary_sha256": program_sha256,
                "nonclaims": [
                    "the V6 receipt alone grants no ledger, settlement, release, or production authority",
                    "this report proves one bounded singleton Spot transition and no maximum-fanout throughput claim",
                ],
                "ok": True,
                "receipt_bytes": len(raw),
                "receipt_profile_id": {runner.SUCCINCT_PROFILE_ID!r},
                "receipt_sha256": hashlib.sha256(raw).hexdigest(),
                "schema": "zenodex/zrpf_source_opened_spot_value_leaf_v6_proof_report/v2",
                "source_envelope_bytes": len(envelope),
                "source_envelope_sha256": hashlib.sha256(envelope).hexdigest(),
                "source_proof_sha256": digest(options["--source-proof"]),
                "statement_hash": "66" * 32,
                "status": "source_opened_spot_value_leaf_v6_succinct_receipt_verified",
                "v6_image_id": image_id,
                "verified_program_manifest_root": "77" * 32,
            }}
        elif role in ("level_one", "level_two"):
            write(options["--receipt-out"], raw)
            child_hash = digest(options["--child"])
            if fault == "child_hash":
                child_hash = "00" * 32
            label = "l1" if role == "level_one" else "l2"
            report = {{
                "child_receipt_sha256": child_hash,
                "image_id": image_id,
                "ok": True,
                "receipt_bytes": len(raw),
                "receipt_sha256": hashlib.sha256(raw).hexdigest(),
                "schema": f"zenodex/zrpf_source_opened_spot_value_aggregate_{{label}}_v6_proof_report/v1",
                "status": f"source_opened_spot_value_aggregate_{{label}}_v6_succinct_receipt_verified",
                "verified_child_count": 1,
            }}
        else:
            admission = b"settlement-admission-journal-v6"
            guest_input = b"settlement-guest-input-v6"
            replay = b"settlement-replay-v6"
            da = b"settlement-da-certificate-v6"
            mutation = json.loads(raw)
            mutation["inner"]["Succinct"]["seal"][1] ^= 1
            mutation_raw = compact(mutation)
            if fault == "bad_mutation":
                mutation_raw = raw
            write(options["--receipt-out"], raw)
            write(options["--journal-out"], admission)
            write(options["--mutation-out"], mutation_raw)
            write(options["--guest-input-out"], guest_input)
            write(options["--replay-out"], replay)
            write(options["--da-certificate-out"], da)
            report = {{
                "action_count": 1,
                "admission_journal_bytes": len(admission),
                "admission_journal_sha256": hashlib.sha256(admission).hexdigest(),
                "consumed_object_count": 1,
                "data_availability_certificate_bytes": len(da),
                "data_availability_certificate_sha256": hashlib.sha256(da).hexdigest(),
                "guest_input_bytes": len(guest_input),
                "guest_input_sha256": hashlib.sha256(guest_input).hexdigest(),
                "image_id": image_id,
                "l2_receipt_sha256": digest(options["--l2-receipt"]),
                "mutation_receipt_sha256": hashlib.sha256(mutation_raw).hexdigest(),
                "mutation_rejected": True,
                "nonclaims": [
                    "the accepted source receipt does not establish an end-user signature scheme",
                    "this local receipt grants no release, governance, Tau-finality, or production authority",
                ],
                "ok": True,
                "receipt_bytes": len(raw),
                "receipt_sha256": hashlib.sha256(raw).hexdigest(),
                "replay_bytes": len(replay),
                "replay_sha256": hashlib.sha256(replay).hexdigest(),
                "schema": "zenodex/zrpf_source_opened_spot_settlement_v6_proof_report/v1",
                "settlement_claim_binding": "88" * 32,
                "settlement_program_id": image_id,
                "settlement_program_manifest_root": "99" * 32,
                "source_envelope_sha256": digest(options["--source-envelope"]),
                "status": "source_opened_spot_settlement_v6_succinct_receipt_verified",
                "succinct_receipt_profile_id": {runner.SUCCINCT_PROFILE_ID!r},
            }}
        if fault == "unknown_report_field":
            report["unexpected"] = True
        print(json.dumps(report, sort_keys=True, separators=(",", ":")))
        """
    )


class FakeChain:
    def __init__(
        self,
        root: Path,
        *,
        fault_role: str | None = None,
        fault: str | None = None,
        wrong_image_role: str | None = None,
        escaped_child: Path | None = None,
    ) -> None:
        self.root = root
        self.scratch = root / "encrypted-scratch"
        self.scratch.mkdir(mode=0o700)
        self.output = root / "candidate-chain"
        self.source_request = root / "source-request.json"
        self.source_proof = root / "source-proof.json"
        self.adapter_receipt = root / "adapter-receipt.json"
        self.source_request.write_bytes(_compact({"request": "spot-v6"}))
        self.source_proof.write_bytes(_compact({"proof": "source-succinct"}))
        self.adapter_receipt.write_bytes(_receipt("adapter"))

        self.programs: dict[str, runner.ProgramPin] = {}
        for role, name in PROGRAM_NAMES.items():
            raw = b"R0BF" + f"{role.replace('_', '-')}-program".encode()
            path = root / name
            path.write_bytes(raw)
            self.programs[role] = runner.ProgramPin(
                path=path,
                sha256=_sha256(raw),
                image_id=IMAGE_IDS[role],
            )

        self.r0vm_path = root / "r0vm"
        _write_executable(
            self.r0vm_path,
            _r0vm_source(IMAGE_IDS, wrong_role=wrong_image_role),
        )
        self.r0vm = runner.ExecutablePin(
            self.r0vm_path,
            _sha256(self.r0vm_path.read_bytes()),
        )
        self.provers: dict[str, runner.ExecutablePin] = {}
        for role in PROGRAM_NAMES:
            path = root / f"prove-{role}"
            _write_executable(
                path,
                _prover_source(
                    role,
                    program_sha256=self.programs[role].sha256,
                    image_id=IMAGE_IDS[role],
                    fault=fault if role == fault_role else None,
                    escaped_child=escaped_child,
                ),
            )
            self.provers[role] = runner.ExecutablePin(path, _sha256(path.read_bytes()))

    def run(self, *, timeout_seconds: int = 10) -> runner.ProofChainResult:
        return runner.run_proof_chain(
            scratch_parent=self.scratch,
            output_directory=self.output,
            r0vm=self.r0vm,
            leaf_prover=self.provers["leaf"],
            level_one_prover=self.provers["level_one"],
            level_two_prover=self.provers["level_two"],
            settlement_prover=self.provers["settlement"],
            source_request=self.source_request,
            source_proof=self.source_proof,
            adapter_receipt=self.adapter_receipt,
            leaf_program=self.programs["leaf"],
            level_one_program=self.programs["level_one"],
            level_two_program=self.programs["level_two"],
            settlement_program=self.programs["settlement"],
            timeout_seconds=timeout_seconds,
        )


def _run_chain_in_child(chain: FakeChain, sender: Connection) -> None:
    try:
        chain.run()
    except BaseException as exc:
        sender.send((type(exc).__name__, str(exc)))
    else:
        sender.send(("accepted", ""))
    finally:
        sender.close()


def _assert_bounded_child_rejection(chain: FakeChain, expected_message: str) -> None:
    context = multiprocessing.get_context("fork")
    receiver, sender = context.Pipe(duplex=False)
    process = context.Process(target=_run_chain_in_child, args=(chain, sender))
    try:
        process.start()
        sender.close()
        process.join(timeout=3.0)
        if process.is_alive():
            process.kill()
            process.join(timeout=1.0)
            pytest.fail("FIFO regression child exceeded its hard timeout")
        assert process.exitcode == 0
        assert receiver.poll(1.0)
        error_type, message = receiver.recv()
        assert error_type == "ProofChainError"
        assert expected_message in message
    finally:
        if process.is_alive():
            process.kill()
            process.join(timeout=1.0)
        sender.close()
        receiver.close()


def test_four_stage_candidate_is_exact_private_and_authority_false(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    chain = FakeChain(tmp_path)
    monkeypatch.setenv("UNRELATED_HOST_SECRET", "must-not-cross-process-boundary")

    result = chain.run()

    assert result.candidate_proof_chain_built is True
    assert result.scoped_local_replay_claim_allowed is False
    assert result.release_authority is False
    assert result.settlement_authority is False
    assert result.production_authority is False
    assert result.artifact_count == len(runner.ARTIFACT_NAMES)
    assert result.report_count == len(runner.STAGE_REPORT_NAMES)
    expected_files = {
        "proof_chain_report.json",
        *(f"artifacts/{name}" for name in runner.ARTIFACT_NAMES),
        *(f"reports/{name}" for name in runner.STAGE_REPORT_NAMES),
    }
    observed = {
        path.relative_to(chain.output).as_posix()
        for path in chain.output.rglob("*")
        if path.is_file()
    }
    assert observed == expected_files
    assert stat.S_IMODE(chain.output.stat().st_mode) == 0o700
    for path in chain.output.rglob("*"):
        expected_mode = 0o700 if path.is_dir() else 0o600
        assert stat.S_IMODE(path.stat().st_mode) == expected_mode
    assert list(chain.scratch.iterdir()) == []

    report = json.loads((chain.output / "proof_chain_report.json").read_bytes())
    assert report["schema"] == runner.REPORT_SCHEMA
    assert report["stage_order"] == list(runner.STAGE_ORDER)
    assert report["candidate_proof_chain_built"] is True
    assert report["proof_byte_determinism_verified"] is False
    assert report["proof_generation_reproducibility_verified"] is False
    assert report["scratch_parent_encryption_verified"] is False
    assert report["independent_retained_replay_verified"] is False
    assert report["network_isolation_verified"] is False
    assert report["runtime_resource_containment_verified"] is False
    assert report["sandbox_authority"] is False
    assert report["same_uid_resistance_verified"] is False
    assert report["crash_durable_publication_verified"] is False
    assert report["source_to_binary_reproducibility_verified"] is False
    assert report["release_authority"] is False
    assert report["settlement_authority"] is False
    assert report["production_authority"] is False
    assert [row["role"] for row in report["executables"]] == list(
        runner.EXECUTABLE_ROLES
    )
    assert [row["artifact"] for row in report["artifacts"]] == list(
        runner.ARTIFACT_NAMES
    )

    artifacts = chain.output / "artifacts"
    for positive, mutation in (
        ("leaf_receipt.json", "leaf_mutation_receipt.json"),
        ("l1_receipt.json", "l1_mutation_receipt.json"),
        ("l2_receipt.json", "l2_mutation_receipt.json"),
        ("settlement_receipt.json", "settlement_mutation_receipt.json"),
    ):
        assert artifacts.joinpath(mutation).read_bytes() == _mutate_receipt(
            artifacts.joinpath(positive).read_bytes()
        )


def test_wrong_executable_pin_rejects_before_any_stage_or_publication(tmp_path: Path) -> None:
    chain = FakeChain(tmp_path)
    chain.provers["leaf"] = replace(chain.provers["leaf"], sha256="00" * 32)

    with pytest.raises(runner.ProofChainError, match="leaf prover SHA-256 mismatch"):
        chain.run()

    assert not chain.output.exists()
    assert list(chain.scratch.iterdir()) == []


def test_ambient_dev_mode_rejects_before_snapshot_or_publication(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    chain = FakeChain(tmp_path)
    monkeypatch.setenv("RISC0_DEV_MODE", "0")

    with pytest.raises(runner.ProofChainError, match="ambient RISC0_DEV_MODE"):
        chain.run()

    assert not chain.output.exists()


def test_r0vm_program_identity_mismatch_rejects_without_publication(tmp_path: Path) -> None:
    chain = FakeChain(tmp_path, wrong_image_role="level_two")

    with pytest.raises(runner.ProofChainError, match="level_two image ID mismatch"):
        chain.run()

    assert not chain.output.exists()
    assert list(chain.scratch.iterdir()) == []


@pytest.mark.parametrize(
    ("role", "fault", "message"),
    [
        ("leaf", "nonzero", "leaf prover returned nonzero"),
        ("leaf", "extra_output", "leaf output inventory mismatch"),
        ("leaf", "fifo_output", "leaf output inventory contains a non-file"),
        ("level_one", "child_hash", "level_one child receipt SHA-256 mismatch"),
        ("settlement", "bad_mutation", "settlement mutation must XOR"),
        ("settlement", "unknown_report_field", "settlement report field set mismatch"),
    ],
)
def test_stage_or_relation_failure_leaves_no_candidate(
    tmp_path: Path, role: str, fault: str, message: str
) -> None:
    chain = FakeChain(tmp_path, fault_role=role, fault=fault)

    with pytest.raises(runner.ProofChainError, match=message):
        chain.run()

    assert not chain.output.exists()
    assert list(chain.scratch.iterdir()) == []


def test_output_limit_kills_prover_group_and_leaves_no_candidate(tmp_path: Path) -> None:
    chain = FakeChain(tmp_path, fault_role="leaf", fault="stdout_overflow")

    with pytest.raises(runner.ProofChainError, match="leaf prover process failed"):
        chain.run()

    assert not chain.output.exists()
    assert list(chain.scratch.iterdir()) == []


def test_timeout_kills_descendants(tmp_path: Path) -> None:
    escaped = tmp_path / "escaped-child"
    chain = FakeChain(
        tmp_path,
        fault_role="leaf",
        fault="timeout",
        escaped_child=escaped,
    )

    with pytest.raises(runner.ProofChainError, match="leaf prover process failed"):
        chain.run(timeout_seconds=1)

    time.sleep(1.7)
    assert not escaped.exists()
    assert not chain.output.exists()


def test_successful_stage_kills_residual_descendants(tmp_path: Path) -> None:
    escaped = tmp_path / "escaped-residual-child"
    chain = FakeChain(
        tmp_path,
        fault_role="leaf",
        fault="residual_child",
        escaped_child=escaped,
    )

    result = chain.run()

    assert result.candidate_proof_chain_built is True
    time.sleep(1.7)
    assert not escaped.exists()


def test_existing_output_is_preserved_without_executing(tmp_path: Path) -> None:
    chain = FakeChain(tmp_path)
    chain.output.mkdir()
    marker = chain.output / "owned"
    marker.write_bytes(b"preexisting")

    with pytest.raises(runner.ProofChainError, match="output directory already exists"):
        chain.run()

    assert marker.read_bytes() == b"preexisting"


def test_publication_race_preserves_racing_output(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    chain = FakeChain(tmp_path)

    def race(_source: Path, destination: Path) -> None:
        destination.mkdir()
        destination.joinpath("racer").write_bytes(b"other-owner")
        raise FileExistsError("simulated publication race")

    monkeypatch.setattr(runner, "_rename_noreplace", race)

    with pytest.raises(runner.ProofChainError, match="atomic candidate publication failed"):
        chain.run()

    assert chain.output.joinpath("racer").read_bytes() == b"other-owner"
    assert list(chain.scratch.iterdir()) == []


def test_fifo_authority_input_rejects_without_blocking(tmp_path: Path) -> None:
    chain = FakeChain(tmp_path)
    fifo = tmp_path / "source-request.fifo"
    os.mkfifo(fifo, 0o600)
    chain.source_request = fifo

    _assert_bounded_child_rejection(chain, "not a bounded regular file")
    assert not chain.output.exists()


def test_fifo_program_rejects_without_blocking(tmp_path: Path) -> None:
    chain = FakeChain(tmp_path)
    fifo = tmp_path / "leaf-program.fifo"
    os.mkfifo(fifo, 0o600)
    chain.programs["leaf"] = replace(chain.programs["leaf"], path=fifo)

    _assert_bounded_child_rejection(chain, "not a bounded regular file")
    assert not chain.output.exists()


def test_fifo_executable_rejects_without_blocking(tmp_path: Path) -> None:
    chain = FakeChain(tmp_path)
    fifo = tmp_path / "r0vm.fifo"
    os.mkfifo(fifo, 0o600)
    chain.r0vm = runner.ExecutablePin(path=fifo, sha256="aa" * 32)

    _assert_bounded_child_rejection(chain, "r0vm executable snapshot failed")
    assert not chain.output.exists()


@pytest.mark.parametrize("raw", [b'{"x":NaN}', b'{"x":Infinity}', b'{"x":1.5}'])
def test_noninteger_json_number_rejects_stably(raw: bytes) -> None:
    with pytest.raises(runner.ProofChainError, match="non-integer JSON number"):
        runner._require_json_object(raw, "authority input")


def test_deep_json_rejects_with_stable_error() -> None:
    raw = b'{"x":' + (b"[" * 80) + b"0" + (b"]" * 80) + b"}"

    with pytest.raises(runner.ProofChainError, match="JSON nesting bound"):
        runner._require_json_object(raw, "authority input")


def test_json_node_bound_rejects_stably(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(runner, "MAX_JSON_NODES", 3)

    with pytest.raises(runner.ProofChainError, match="JSON node bound"):
        runner._require_json_object(b'{"a":[1,2,3]}', "authority input")


def test_post_commit_descriptor_close_error_does_not_report_false_reject(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    source = tmp_path / "candidate"
    destination = tmp_path / "published"
    source.mkdir()
    source.joinpath("artifact").write_bytes(b"governed")
    original_close = os.close
    close_count = 0

    def close_with_one_post_commit_error(descriptor: int) -> None:
        nonlocal close_count
        close_count += 1
        original_close(descriptor)
        if close_count == 2:
            raise OSError("simulated close error after rename")

    monkeypatch.setattr(runner.os, "close", close_with_one_post_commit_error)

    runner._atomic_publish_candidate(source, destination)

    assert not source.exists()
    assert destination.joinpath("artifact").read_bytes() == b"governed"


def test_scratch_parent_must_be_private(tmp_path: Path) -> None:
    chain = FakeChain(tmp_path)
    chain.scratch.chmod(0o755)

    with pytest.raises(runner.ProofChainError, match="scratch parent mode must be 0700"):
        chain.run()

    assert not chain.output.exists()


def test_symlinked_authority_input_rejects(tmp_path: Path) -> None:
    chain = FakeChain(tmp_path)
    real = chain.source_request
    link = tmp_path / "source-request-link.json"
    link.symlink_to(real)
    chain.source_request = link

    with pytest.raises(runner.ProofChainError, match="source request is unavailable or symlinked"):
        chain.run()

    assert not chain.output.exists()
