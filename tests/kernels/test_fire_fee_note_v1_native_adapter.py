from __future__ import annotations

import json
import importlib.util
import subprocess
import sys
from pathlib import Path
from types import ModuleType, SimpleNamespace

import pytest

from src.fire.registry.bundle_v1 import load_fire_registry_bundle, write_fire_registry_bundle
from src.fire.runtime.fee_note_v1 import FeeNoteTerms, build_manifest, compile_terms, render_object_card
from src.fire.verifier.settlement_v1 import (
    FireSettlementPacket,
    FireVerifierReceipt,
    fire_witness_binding_hash,
    verify_fire_settlement_packet,
)


MODEL = Path("src/kernels/dex/fire_fee_note_v1.yaml")
ADAPTER = "src.fire.runtime.fee_note_v1_native_adapter:make_simulation_adapter"


def _esso_available() -> bool:
    return importlib.util.find_spec("ESSO") is not None


def _receipt_for_bundle(
    bundle_dir: Path,
    *,
    holder_delta: int,
    writer_delta: int,
    witness_final: int,
) -> dict[str, object]:
    bundle_manifest, _bundle_file_sha256, object_manifest, object_instance, _object_lock = load_fire_registry_bundle(bundle_dir)
    return FireVerifierReceipt.build(
        object_hash=object_manifest.manifest_hash,
        instance_hash=object_instance.instance_hash,
        cert_sha256=object_manifest.cert_sha256,
        holder_delta=holder_delta,
        writer_delta=writer_delta,
        command_tag="firev_accept_and_settle",
        object_name=object_manifest.object_name,
        object_version=object_manifest.object_version,
        bundle_hash=bundle_manifest.bundle_hash,
        witness_hash=fire_witness_binding_hash({"witness_final": witness_final}),
    ).to_dict()


def _install_fake_interpreter(monkeypatch):
    esso_mod = ModuleType("ESSO")
    kernel_mod = ModuleType("ESSO.kernel")
    interp_mod = ModuleType("ESSO.kernel.interpreter")

    class StepOk:
        def __init__(self, *, state, effects):
            self.state = state
            self.effects = effects

    class StepError:
        def __init__(self, *, code: str, message: str):
            self.code = code
            self.message = message

    interp_mod.StepOk = StepOk
    interp_mod.StepError = StepError
    kernel_mod.interpreter = interp_mod
    esso_mod.kernel = kernel_mod

    monkeypatch.setitem(sys.modules, "ESSO", esso_mod)
    monkeypatch.setitem(sys.modules, "ESSO.kernel", kernel_mod)
    monkeypatch.setitem(sys.modules, "ESSO.kernel.interpreter", interp_mod)
    return interp_mod


@pytest.mark.skipif(not _esso_available(), reason="ESSO module unavailable")
def test_fire_fee_note_native_adapter_shell_lint_and_verify(tmp_path: Path) -> None:
    lint_path = tmp_path / "shell_lint.json"
    verify_path = tmp_path / "shell_verify.json"

    subprocess.check_call(
        [
            "python3",
            "-m",
            "ESSO",
            "shell-lint",
            str(MODEL),
            "--adapter",
            ADAPTER,
            "--output",
            str(lint_path),
        ]
    )
    lint = json.loads(lint_path.read_text(encoding="utf-8"))
    assert lint.get("ok") is True

    subprocess.check_call(
        [
            "python3",
            "-m",
            "ESSO",
            "verify-shell",
            str(MODEL),
            "--adapter",
            ADAPTER,
            "--traces",
            "16",
            "--max-steps",
            "8",
            "--determinism-trials",
            "2",
            "--output",
            str(verify_path),
        ]
    )
    verify = json.loads(verify_path.read_text(encoding="utf-8"))
    assert verify.get("ok") is True


def test_fire_fee_note_native_adapter_unknown_action(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.fire.runtime.fee_note_v1_native_adapter import make_adapter

    adapter = make_adapter(ir={"schema": "fake"})
    adapter.reset(
        state={
            "artifact_lower": 0,
            "artifact_upper": 0,
            "cap_index": 0,
            "holder_delta": 0,
            "holder_posted": 0,
            "n_notional": 0,
            "phase": "Idle",
            "source_upper": 0,
            "witness_final": 0,
            "writer_delta": 0,
            "writer_posted": 0,
        }
    )
    result = adapter.apply(SimpleNamespace(tag="bogus", args={}))
    assert isinstance(result, interp_mod.StepError)
    assert result.code == "UnknownAction"


def test_fire_fee_note_native_adapter_guard_false(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.fire.runtime.fee_note_v1_native_adapter import make_adapter

    adapter = make_adapter(ir={"schema": "fake"})
    adapter.reset(
        state={
            "artifact_lower": 0,
            "artifact_upper": 20,
            "cap_index": 7,
            "holder_delta": 0,
            "holder_posted": 0,
            "n_notional": 10,
            "phase": "Compiled",
            "source_upper": 2,
            "witness_final": 0,
            "writer_delta": 0,
            "writer_posted": 0,
        }
    )
    result = adapter.apply(
        SimpleNamespace(
            tag="firev_accept_and_settle",
            args={
                "witness_final_in": 2,
                "holder_posted_in": 0,
                "writer_posted_in": 19,
            },
        )
    )
    assert isinstance(result, interp_mod.StepError)
    assert result.code == "GuardFalse"


def test_fire_fee_note_native_adapter_accepts_persisted_bundle(monkeypatch, tmp_path: Path) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.fire.runtime.fee_note_v1_native_adapter import make_adapter

    artifact = compile_terms(FeeNoteTerms(n_notional=10, cap_index=7, source_upper=2))
    bundle_dir = tmp_path / "fee_bundle"
    bundle_manifest, bundle_file_sha256 = write_fire_registry_bundle(
        bundle_dir,
        artifact=artifact,
        build_manifest=build_manifest,
        render_object_card=render_object_card,
    )

    adapter = make_adapter(ir={"schema": "fake"})
    adapter.reset(
        state={
            "artifact_lower": artifact.artifact_lower,
            "artifact_upper": artifact.artifact_upper,
            "cap_index": artifact.terms.cap_index,
            "holder_delta": 0,
            "holder_posted": 0,
            "n_notional": artifact.terms.n_notional,
            "phase": "Compiled",
            "source_upper": artifact.terms.source_upper,
            "witness_final": 0,
            "writer_delta": 0,
            "writer_posted": 0,
        }
    )
    result = adapter.apply(
        SimpleNamespace(
            tag="firev_accept_and_settle",
            args={
                "witness_final_in": 2,
                "holder_posted_in": 0,
                "writer_posted_in": 20,
                "persisted_bundle_dir": str(bundle_dir),
                "expected_bundle_hash": bundle_manifest.bundle_hash,
                "expected_bundle_file_sha256": bundle_file_sha256,
                "expected_cert_sha256": artifact.cert_sha256,
                "verifier_receipt": _receipt_for_bundle(
                    bundle_dir,
                    holder_delta=20,
                    writer_delta=-20,
                    witness_final=2,
                ),
            },
        )
    )
    assert isinstance(result, interp_mod.StepOk)
    assert result.state["holder_delta"] == 20
    assert result.state["writer_delta"] == -20
    effects = dict(adapter.drain_effects())
    assert effects["firev_accept"] is True
    assert effects["payoff_out"] == 20
    assert effects["verifier_receipt"]["bundle_hash"] == bundle_manifest.bundle_hash
    assert effects["verifier_receipt"]["holder_delta"] == 20
    packet = FireSettlementPacket.from_dict(effects["settlement_packet"])
    assert verify_fire_settlement_packet(
        packet,
        expected_bundle_hash=bundle_manifest.bundle_hash,
        expected_witness_hash=fire_witness_binding_hash({"witness_final": 2}),
        expected_command_tag="firev_accept_and_settle",
    ) == (True, None)
    assert dict(adapter.drain_effects()) == {}


def test_fire_fee_note_native_adapter_rejects_non_bool_firev_accept_effect(
    monkeypatch,
    tmp_path: Path,
) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    import src.fire.runtime.fee_note_v1_native_adapter as adapter_mod

    artifact = compile_terms(FeeNoteTerms(n_notional=10, cap_index=7, source_upper=2))
    bundle_dir = tmp_path / "fee_bundle"
    bundle_manifest, bundle_file_sha256 = write_fire_registry_bundle(
        bundle_dir,
        artifact=artifact,
        build_manifest=build_manifest,
        render_object_card=render_object_card,
    )

    def _string_firev_accept(adapter, effect_id: str, _value) -> None:
        adapter._pending_effects[effect_id] = "false"

    monkeypatch.setitem(adapter_mod.EFFECT_HANDLERS, "firev_accept", _string_firev_accept)

    adapter = adapter_mod.make_adapter(ir={"schema": "fake"})
    adapter.reset(
        state={
            "artifact_lower": artifact.artifact_lower,
            "artifact_upper": artifact.artifact_upper,
            "cap_index": artifact.terms.cap_index,
            "holder_delta": 0,
            "holder_posted": 0,
            "n_notional": artifact.terms.n_notional,
            "phase": "Compiled",
            "source_upper": artifact.terms.source_upper,
            "witness_final": 0,
            "writer_delta": 0,
            "writer_posted": 0,
        }
    )
    result = adapter.apply(
        SimpleNamespace(
            tag="firev_accept_and_settle",
            args={
                "witness_final_in": 2,
                "holder_posted_in": 0,
                "writer_posted_in": 20,
                "persisted_bundle_dir": str(bundle_dir),
                "expected_bundle_hash": bundle_manifest.bundle_hash,
                "expected_bundle_file_sha256": bundle_file_sha256,
                "expected_cert_sha256": artifact.cert_sha256,
                "verifier_receipt": _receipt_for_bundle(
                    bundle_dir,
                    holder_delta=20,
                    writer_delta=-20,
                    witness_final=2,
                ),
            },
        )
    )

    assert isinstance(result, interp_mod.StepError)
    assert result.code == "GuardFalse"
    assert "firev_accept must be a bool" in result.message
    assert adapter.get_state()["holder_delta"] == 0
    assert adapter.get_state()["writer_delta"] == 0
    assert dict(adapter.drain_effects()) == {}


def test_fire_fee_note_native_adapter_rejects_missing_persisted_bundle_receipt(monkeypatch, tmp_path: Path) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.fire.runtime.fee_note_v1_native_adapter import make_adapter

    artifact = compile_terms(FeeNoteTerms(n_notional=10, cap_index=7, source_upper=2))
    bundle_dir = tmp_path / "fee_bundle"
    bundle_manifest, bundle_file_sha256 = write_fire_registry_bundle(
        bundle_dir,
        artifact=artifact,
        build_manifest=build_manifest,
        render_object_card=render_object_card,
    )

    adapter = make_adapter(ir={"schema": "fake"})
    adapter.reset(
        state={
            "artifact_lower": artifact.artifact_lower,
            "artifact_upper": artifact.artifact_upper,
            "cap_index": artifact.terms.cap_index,
            "holder_delta": 0,
            "holder_posted": 0,
            "n_notional": artifact.terms.n_notional,
            "phase": "Compiled",
            "source_upper": artifact.terms.source_upper,
            "witness_final": 0,
            "writer_delta": 0,
            "writer_posted": 0,
        }
    )
    result = adapter.apply(
        SimpleNamespace(
            tag="firev_accept_and_settle",
            args={
                "witness_final_in": 2,
                "holder_posted_in": 0,
                "writer_posted_in": 20,
                "persisted_bundle_dir": str(bundle_dir),
                "expected_bundle_hash": bundle_manifest.bundle_hash,
                "expected_bundle_file_sha256": bundle_file_sha256,
                "expected_cert_sha256": artifact.cert_sha256,
            },
        )
    )
    assert isinstance(result, interp_mod.StepError)
    assert result.code == "GuardFalse"
    assert "verifier receipt missing" in result.message


def test_fire_fee_note_native_adapter_rejects_missing_persisted_bundle_dir(monkeypatch) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.fire.runtime.fee_note_v1_native_adapter import make_adapter

    artifact = compile_terms(FeeNoteTerms(n_notional=10, cap_index=7, source_upper=2))
    adapter = make_adapter(ir={"schema": "fake"})
    adapter.reset(
        state={
            "artifact_lower": artifact.artifact_lower,
            "artifact_upper": artifact.artifact_upper,
            "cap_index": artifact.terms.cap_index,
            "holder_delta": 0,
            "holder_posted": 0,
            "n_notional": artifact.terms.n_notional,
            "phase": "Compiled",
            "source_upper": artifact.terms.source_upper,
            "witness_final": 0,
            "writer_delta": 0,
            "writer_posted": 0,
        }
    )
    result = adapter.apply(
        SimpleNamespace(
            tag="firev_accept_and_settle",
            args={
                "witness_final_in": 2,
                "holder_posted_in": 0,
                "writer_posted_in": 20,
            },
        )
    )
    assert isinstance(result, interp_mod.StepError)
    assert result.code == "GuardFalse"
    assert "persisted bundle dir missing" in result.message


def test_fire_fee_note_native_adapter_rejects_witness_binding_mismatch(monkeypatch, tmp_path: Path) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.fire.runtime.fee_note_v1_native_adapter import make_adapter

    artifact = compile_terms(FeeNoteTerms(n_notional=10, cap_index=7, source_upper=2))
    bundle_dir = tmp_path / "fee_bundle"
    bundle_manifest, bundle_file_sha256 = write_fire_registry_bundle(
        bundle_dir,
        artifact=artifact,
        build_manifest=build_manifest,
        render_object_card=render_object_card,
    )

    adapter = make_adapter(ir={"schema": "fake"})
    adapter.reset(
        state={
            "artifact_lower": artifact.artifact_lower,
            "artifact_upper": artifact.artifact_upper,
            "cap_index": artifact.terms.cap_index,
            "holder_delta": 0,
            "holder_posted": 0,
            "n_notional": artifact.terms.n_notional,
            "phase": "Compiled",
            "source_upper": artifact.terms.source_upper,
            "witness_final": 0,
            "writer_delta": 0,
            "writer_posted": 0,
        }
    )
    result = adapter.apply(
        SimpleNamespace(
            tag="firev_accept_and_settle",
            args={
                "witness_final_in": 2,
                "holder_posted_in": 0,
                "writer_posted_in": 20,
                "persisted_bundle_dir": str(bundle_dir),
                "expected_bundle_hash": bundle_manifest.bundle_hash,
                "expected_bundle_file_sha256": bundle_file_sha256,
                "expected_cert_sha256": artifact.cert_sha256,
                "verifier_receipt": _receipt_for_bundle(
                    bundle_dir,
                    holder_delta=20,
                    writer_delta=-20,
                    witness_final=3,
                ),
            },
        )
    )
    assert isinstance(result, interp_mod.StepError)
    assert result.code == "GuardFalse"
    assert "witness_hash_mismatch" in result.message


def test_fire_fee_note_native_adapter_rejects_bad_persisted_bundle_hash(monkeypatch, tmp_path: Path) -> None:
    interp_mod = _install_fake_interpreter(monkeypatch)
    from src.fire.runtime.fee_note_v1_native_adapter import make_adapter

    artifact = compile_terms(FeeNoteTerms(n_notional=10, cap_index=7, source_upper=2))
    bundle_dir = tmp_path / "fee_bundle"
    write_fire_registry_bundle(
        bundle_dir,
        artifact=artifact,
        build_manifest=build_manifest,
        render_object_card=render_object_card,
    )

    adapter = make_adapter(ir={"schema": "fake"})
    adapter.reset(
        state={
            "artifact_lower": artifact.artifact_lower,
            "artifact_upper": artifact.artifact_upper,
            "cap_index": artifact.terms.cap_index,
            "holder_delta": 0,
            "holder_posted": 0,
            "n_notional": artifact.terms.n_notional,
            "phase": "Compiled",
            "source_upper": artifact.terms.source_upper,
            "witness_final": 0,
            "writer_delta": 0,
            "writer_posted": 0,
        }
    )
    result = adapter.apply(
        SimpleNamespace(
            tag="firev_accept_and_settle",
            args={
                "witness_final_in": 2,
                "holder_posted_in": 0,
                "writer_posted_in": 20,
                "persisted_bundle_dir": str(bundle_dir),
                "expected_bundle_hash": "sha256:" + "0" * 64,
                "expected_cert_sha256": artifact.cert_sha256,
            },
        )
    )
    assert isinstance(result, interp_mod.StepError)
    assert result.code == "GuardFalse"
    assert "expected_bundle_hash_mismatch" in result.message
