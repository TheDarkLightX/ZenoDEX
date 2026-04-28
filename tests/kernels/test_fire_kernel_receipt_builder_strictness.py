from __future__ import annotations

import json
from pathlib import Path

import pytest

from src.fire.kernel import kernel_replay_receipt_v1 as replay_mod
from src.fire.kernel import kernel_settlement_receipt_v1 as settlement_mod
from src.fire.registry.bundle_v1 import write_fire_registry_bundle
from src.fire.registry.instance_v1 import FireObjectInstanceManifest
from src.fire.registry.object_manifest_v1 import FireObjectManifest
from src.fire.registry.replay_input_v1 import FireReplayInput
from src.fire.runtime.burn_boost_call_v1 import BurnBoostCallTerms, build_manifest, compile_terms, render_object_card


_SHA0 = "sha256:" + ("0" * 64)
_SHA1 = "sha256:" + ("1" * 64)
_SHA2 = "sha256:" + ("2" * 64)
_SHA3 = "sha256:" + ("3" * 64)
_SHA4 = "sha256:" + ("4" * 64)


def _bundle_inputs(tmp_path: Path) -> tuple[FireObjectManifest, FireObjectInstanceManifest, FireReplayInput]:
    artifact = compile_terms(BurnBoostCallTerms(n_notional=10, strike_index=4, cap_index=3, source_upper=9))
    bundle_dir = tmp_path / "burn_bundle"
    write_fire_registry_bundle(
        bundle_dir,
        artifact=artifact,
        build_manifest=build_manifest,
        render_object_card=render_object_card,
    )
    object_manifest = FireObjectManifest.from_dict(
        json.loads((bundle_dir / "object_manifest.json").read_text(encoding="utf-8"))
    )
    object_instance = FireObjectInstanceManifest.from_dict(
        json.loads((bundle_dir / "instance_manifest.json").read_text(encoding="utf-8"))
    )
    replay_input = FireReplayInput.from_dict(json.loads((bundle_dir / "replay_input.json").read_text(encoding="utf-8")))
    return object_manifest, object_instance, replay_input


def test_kernel_settlement_receipt_builder_rejects_non_bool_firev_accept_effect(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    object_manifest, object_instance, replay_input = _bundle_inputs(tmp_path)

    def _fake_run_kernel_settlement(**_kwargs):
        return (
            {"phase": "Settled", "holder_delta": 0, "writer_delta": 0},
            {"payoff_out": 0, "firev_accept": "false"},
            "firev_accept_and_settle",
            {"witness_final_in": 7, "holder_posted_in": 0, "writer_posted_in": 30},
        )

    monkeypatch.setattr(settlement_mod, "_run_kernel_settlement", _fake_run_kernel_settlement)

    with pytest.raises(TypeError, match="settlement_effects.firev_accept must be a bool"):
        settlement_mod.build_fire_kernel_settlement_receipt(
            object_manifest=object_manifest,
            object_instance=object_instance,
            replay_input=replay_input,
            replay_input_sha256=_SHA0,
            kernel_receipt_sha256=_SHA1,
            kernel_eval_receipt_sha256=_SHA2,
        )


def test_kernel_settlement_receipt_builder_rejects_string_delta(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    object_manifest, object_instance, replay_input = _bundle_inputs(tmp_path)

    def _fake_run_kernel_settlement(**_kwargs):
        return (
            {"phase": "Settled", "holder_delta": "0", "writer_delta": 0},
            {"payoff_out": 0, "firev_accept": True},
            "firev_accept_and_settle",
            {"witness_final_in": 7, "holder_posted_in": 0, "writer_posted_in": 30},
        )

    monkeypatch.setattr(settlement_mod, "_run_kernel_settlement", _fake_run_kernel_settlement)

    with pytest.raises(TypeError, match="settlement_state.holder_delta must be an int"):
        settlement_mod.build_fire_kernel_settlement_receipt(
            object_manifest=object_manifest,
            object_instance=object_instance,
            replay_input=replay_input,
            replay_input_sha256=_SHA0,
            kernel_receipt_sha256=_SHA1,
            kernel_eval_receipt_sha256=_SHA2,
        )


def test_kernel_replay_receipt_builder_rejects_non_bool_firev_accept_effect(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    object_manifest, object_instance, replay_input = _bundle_inputs(tmp_path)

    def _fake_run_kernel_replay(**_kwargs):
        return (
            {"phase": "Compiled", "holder_delta": 0, "writer_delta": 0},
            {"compiled_lower": 0, "compiled_upper": 30},
            "compile_burn_boost_call",
            {"n_notional": 10, "strike_index": 4, "cap_index": 3, "source_upper": 9},
            {"phase": "Settled", "holder_delta": 0, "writer_delta": 0},
            {"payoff_out": 0, "firev_accept": "false"},
            "firev_accept_and_settle",
            {"witness_final_in": 7, "holder_posted_in": 0, "writer_posted_in": 30},
        )

    monkeypatch.setattr(replay_mod, "_run_kernel_replay", _fake_run_kernel_replay)

    with pytest.raises(TypeError, match="settlement_effects.firev_accept must be a bool"):
        replay_mod.build_fire_kernel_replay_receipt(
            object_manifest=object_manifest,
            object_instance=object_instance,
            replay_input=replay_input,
            replay_input_sha256=_SHA0,
            compile_receipt_sha256=_SHA1,
            kernel_receipt_sha256=_SHA2,
            kernel_eval_receipt_sha256=_SHA3,
            kernel_settlement_receipt_sha256=_SHA4,
        )


def test_kernel_replay_receipt_builder_rejects_string_payoff_out(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    object_manifest, object_instance, replay_input = _bundle_inputs(tmp_path)

    def _fake_run_kernel_replay(**_kwargs):
        return (
            {"phase": "Compiled", "holder_delta": 0, "writer_delta": 0},
            {"compiled_lower": 0, "compiled_upper": 30},
            "compile_burn_boost_call",
            {"n_notional": 10, "strike_index": 4, "cap_index": 3, "source_upper": 9},
            {"phase": "Settled", "holder_delta": 0, "writer_delta": 0},
            {"payoff_out": "0", "firev_accept": True},
            "firev_accept_and_settle",
            {"witness_final_in": 7, "holder_posted_in": 0, "writer_posted_in": 30},
        )

    monkeypatch.setattr(replay_mod, "_run_kernel_replay", _fake_run_kernel_replay)

    with pytest.raises(TypeError, match="settlement_effects.payoff_out must be an int"):
        replay_mod.build_fire_kernel_replay_receipt(
            object_manifest=object_manifest,
            object_instance=object_instance,
            replay_input=replay_input,
            replay_input_sha256=_SHA0,
            compile_receipt_sha256=_SHA1,
            kernel_receipt_sha256=_SHA2,
            kernel_eval_receipt_sha256=_SHA3,
            kernel_settlement_receipt_sha256=_SHA4,
        )
