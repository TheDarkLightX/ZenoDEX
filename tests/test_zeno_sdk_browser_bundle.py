from __future__ import annotations

import json
import subprocess
from pathlib import Path

import pytest

from src.integration.zeno_ledger_profile import sample_zeno_sovereign_testnet_profile_v0
from src.integration.zeno_ledger_signature import build_bls_signed_artifact_envelope_v0
from src.integration.zeno_ledger_v0 import hash_v0
from src.integration.zeno_sdk_browser_bundle_v0 import (
    BROWSER_CHECKPOINT_BUNDLE_SCHEMA_V0,
    BROWSER_WALLET_SYNC_STATE_SCHEMA_V0,
    validate_browser_checkpoint_bundle_v0,
    validate_wallet_sync_state_v0,
    wallet_sync_state_v0,
)
from tests.test_check_zeno_ledger_light_client_checkpoint import (
    TEST_BLS_PRIVATE_KEY_A,
    TEST_BLS_PRIVATE_KEY_B,
    _fixture,
    _write_json,
)
from tools.build_zeno_sdk_browser_bundle import build_browser_bundle_from_files, main
from tools.zeno_ledger_verify import ZERO_ROOT

ROOT = Path(__file__).resolve().parents[1]


def _write_fixture_files(tmp_path: Path) -> tuple[Path, Path, Path, Path, list[Path]]:
    headers_dir, bodies_dir, checkpoints_dir, registry, envelopes = _fixture(tmp_path)
    registry_path = tmp_path / "registry.json"
    envelope_a_path = tmp_path / "checkpoint.a.sig.json"
    envelope_b_path = tmp_path / "checkpoint.b.sig.json"
    _write_json(registry_path, registry)
    _write_json(envelope_a_path, envelopes[0])
    _write_json(envelope_b_path, envelopes[1])
    return headers_dir, bodies_dir, checkpoints_dir, registry_path, [envelope_a_path, envelope_b_path]


def test_build_browser_bundle_accepts_verified_light_client_fixture(tmp_path: Path) -> None:
    headers_dir, bodies_dir, checkpoints_dir, registry_path, envelope_paths = _write_fixture_files(tmp_path)

    bundle = build_browser_bundle_from_files(
        headers_dir=headers_dir,
        bodies_dir=bodies_dir,
        checkpoints_dir=checkpoints_dir,
        registry_path=registry_path,
        envelope_paths=envelope_paths,
        from_height=1,
        to_height=2,
    )

    assert bundle["schema"] == BROWSER_CHECKPOINT_BUNDLE_SCHEMA_V0
    assert bundle["capabilities"]["python_bls_quorum_verified"] is True
    assert bundle["capabilities"]["browser_bls_quorum_verified"] is False
    assert bundle["capabilities"]["proof_authority_satisfied"] is False
    assert bundle["capabilities"]["proof_authority_capable"] is False
    assert bundle["capabilities"]["settlement_authority"] is False
    assert bundle["capabilities"]["production_authority"] is False
    assert bundle["capabilities"]["python_structural_range_verified"] is True
    assert bundle["capabilities"]["python_range_replay_verified"] is False
    assert bundle["capabilities"]["browser_shape_and_hash_available"] is True
    assert bundle["capabilities"]["browser_shape_and_hash_verified"] is False
    assert bundle["capabilities"]["browser_header_chain_available"] is True
    assert bundle["capabilities"]["browser_header_chain_verified"] is False
    assert bundle["capabilities"]["browser_range_replay_available"] is False
    assert bundle["capabilities"]["browser_range_replay_verified"] is False
    assert bundle["verification_summary"]["proof_authority_required"] is False
    assert bundle["verification_summary"]["proof_authority_satisfied"] is False
    assert bundle["verification_summary"]["proof_authority_capable"] is False
    assert bundle["verification_summary"]["checkpoint_hash"].startswith("0x")
    validate_browser_checkpoint_bundle_v0(bundle)


def test_browser_bundle_rejects_tampered_checkpoint(tmp_path: Path) -> None:
    headers_dir, bodies_dir, checkpoints_dir, registry_path, envelope_paths = _write_fixture_files(tmp_path)
    bundle = build_browser_bundle_from_files(
        headers_dir=headers_dir,
        bodies_dir=bodies_dir,
        checkpoints_dir=checkpoints_dir,
        registry_path=registry_path,
        envelope_paths=envelope_paths,
        from_height=1,
        to_height=2,
    )
    bundle["target_checkpoint"]["height"] = 3

    try:
        validate_browser_checkpoint_bundle_v0(bundle)
    except ValueError as exc:
        assert "hash mismatch" in str(exc)
    else:
        raise AssertionError("tampered browser bundle was accepted")


def test_browser_bundle_rejects_broken_header_chain_with_recomputed_hash(tmp_path: Path) -> None:
    headers_dir, bodies_dir, checkpoints_dir, registry_path, envelope_paths = _write_fixture_files(tmp_path)
    bundle = build_browser_bundle_from_files(
        headers_dir=headers_dir,
        bodies_dir=bodies_dir,
        checkpoints_dir=checkpoints_dir,
        registry_path=registry_path,
        envelope_paths=envelope_paths,
        from_height=1,
        to_height=2,
    )
    bundle["header_chain"][1]["prev_header_hash"] = ZERO_ROOT
    body = {key: bundle[key] for key in bundle if key != "bundle_hash"}
    bundle["bundle_hash"] = hash_v0("browser_checkpoint_bundle_v0", body)

    try:
        validate_browser_checkpoint_bundle_v0(bundle)
    except ValueError as exc:
        assert "prev_header_hash" in str(exc)
    else:
        raise AssertionError("broken browser bundle header chain was accepted")


def test_browser_bundle_rejects_string_summary_weight_with_recomputed_hash(tmp_path: Path) -> None:
    headers_dir, bodies_dir, checkpoints_dir, registry_path, envelope_paths = _write_fixture_files(tmp_path)
    bundle = build_browser_bundle_from_files(
        headers_dir=headers_dir,
        bodies_dir=bodies_dir,
        checkpoints_dir=checkpoints_dir,
        registry_path=registry_path,
        envelope_paths=envelope_paths,
        from_height=1,
        to_height=2,
    )
    bundle["verification_summary"]["accepted_weight"] = str(bundle["verification_summary"]["accepted_weight"])
    body = {key: bundle[key] for key in bundle if key != "bundle_hash"}
    bundle["bundle_hash"] = hash_v0("browser_checkpoint_bundle_v0", body)

    try:
        validate_browser_checkpoint_bundle_v0(bundle)
    except ValueError as exc:
        assert "accepted_weight" in str(exc)
    else:
        raise AssertionError("string accepted_weight was accepted")


def test_browser_bundle_rejects_unknown_summary_field_with_recomputed_hash(tmp_path: Path) -> None:
    headers_dir, bodies_dir, checkpoints_dir, registry_path, envelope_paths = _write_fixture_files(tmp_path)
    bundle = build_browser_bundle_from_files(
        headers_dir=headers_dir,
        bodies_dir=bodies_dir,
        checkpoints_dir=checkpoints_dir,
        registry_path=registry_path,
        envelope_paths=envelope_paths,
        from_height=1,
        to_height=2,
    )
    bundle["verification_summary"]["extra"] = True
    body = {key: bundle[key] for key in bundle if key != "bundle_hash"}
    bundle["bundle_hash"] = hash_v0("browser_checkpoint_bundle_v0", body)

    try:
        validate_browser_checkpoint_bundle_v0(bundle)
    except ValueError as exc:
        assert "verification summary keys mismatch" in str(exc)
    else:
        raise AssertionError("unknown verification summary field was accepted")


def test_browser_bundle_rejects_false_capability_with_recomputed_hash(tmp_path: Path) -> None:
    headers_dir, bodies_dir, checkpoints_dir, registry_path, envelope_paths = _write_fixture_files(tmp_path)
    bundle = build_browser_bundle_from_files(
        headers_dir=headers_dir,
        bodies_dir=bodies_dir,
        checkpoints_dir=checkpoints_dir,
        registry_path=registry_path,
        envelope_paths=envelope_paths,
        from_height=1,
        to_height=2,
    )
    bundle["capabilities"]["python_bls_quorum_verified"] = False
    body = {key: bundle[key] for key in bundle if key != "bundle_hash"}
    bundle["bundle_hash"] = hash_v0("browser_checkpoint_bundle_v0", body)

    try:
        validate_browser_checkpoint_bundle_v0(bundle)
    except ValueError as exc:
        assert "python BLS quorum capability" in str(exc)
    else:
        raise AssertionError("false python BLS capability was accepted")


def test_browser_bundle_rejects_forged_proof_authority_capability(tmp_path: Path) -> None:
    headers_dir, bodies_dir, checkpoints_dir, registry_path, envelope_paths = _write_fixture_files(
        tmp_path
    )
    bundle = build_browser_bundle_from_files(
        headers_dir=headers_dir,
        bodies_dir=bodies_dir,
        checkpoints_dir=checkpoints_dir,
        registry_path=registry_path,
        envelope_paths=envelope_paths,
        from_height=1,
        to_height=2,
    )
    bundle["capabilities"]["proof_authority_satisfied"] = True
    body = {key: bundle[key] for key in bundle if key != "bundle_hash"}
    bundle["bundle_hash"] = hash_v0("browser_checkpoint_bundle_v0", body)

    with pytest.raises(ValueError, match="proof_authority_satisfied must be false"):
        validate_browser_checkpoint_bundle_v0(bundle)


def test_browser_bundle_rejects_structural_report_promoted_to_range_replay(
    tmp_path: Path,
) -> None:
    headers_dir, bodies_dir, checkpoints_dir, registry_path, envelope_paths = _write_fixture_files(
        tmp_path
    )
    bundle = build_browser_bundle_from_files(
        headers_dir=headers_dir,
        bodies_dir=bodies_dir,
        checkpoints_dir=checkpoints_dir,
        registry_path=registry_path,
        envelope_paths=envelope_paths,
        from_height=1,
        to_height=2,
    )
    bundle["verification_summary"]["python_range_replay_verified"] = True
    body = {key: bundle[key] for key in bundle if key != "bundle_hash"}
    bundle["bundle_hash"] = hash_v0("browser_checkpoint_bundle_v0", body)

    with pytest.raises(ValueError, match="range replay verification must remain false"):
        validate_browser_checkpoint_bundle_v0(bundle)


def test_browser_bundle_rejects_proof_required_profile(tmp_path: Path) -> None:
    headers_dir, bodies_dir, checkpoints_dir, registry_path, envelope_paths = _write_fixture_files(
        tmp_path
    )
    profile_path = tmp_path / "proof-required-profile.json"
    _write_json(
        profile_path,
        sample_zeno_sovereign_testnet_profile_v0(
            chain_id="zeno-ledger-light-client-testnet-0",
            config_digest=hash_v0("light_client_test_root", {"label": "config"}),
            sequencer_set_hash=hash_v0(
                "light_client_test_root", {"label": "sequencer-set"}
            ),
            token_symbol="tZENO",
            token_asset_id=hash_v0("light_client_test_root", {"label": "token"}),
            proof_required=True,
        ),
    )

    with pytest.raises(ValueError, match="light client checkpoint verification rejected"):
        build_browser_bundle_from_files(
            headers_dir=headers_dir,
            bodies_dir=bodies_dir,
            checkpoints_dir=checkpoints_dir,
            registry_path=registry_path,
            envelope_paths=envelope_paths,
            from_height=1,
            to_height=2,
            profile_path=profile_path,
        )


def test_wallet_sync_state_rejects_rollback(tmp_path: Path) -> None:
    headers_dir, bodies_dir, checkpoints_dir, registry_path, envelope_paths = _write_fixture_files(tmp_path)
    bundle = build_browser_bundle_from_files(
        headers_dir=headers_dir,
        bodies_dir=bodies_dir,
        checkpoints_dir=checkpoints_dir,
        registry_path=registry_path,
        envelope_paths=envelope_paths,
        from_height=1,
        to_height=2,
    )
    current = wallet_sync_state_v0(
        current_state=None,
        checkpoint_bundle=bundle,
        surface="zusd",
        updated_at_ms=1_778_730_000_000,
    )
    validate_wallet_sync_state_v0(current)
    assert current["schema"] == BROWSER_WALLET_SYNC_STATE_SCHEMA_V0
    assert current["height"] == 2

    lower = dict(current)
    lower["height"] = 3
    lower["state_hash"] = current["state_hash"]
    try:
        wallet_sync_state_v0(
            current_state=lower,
            checkpoint_bundle=bundle,
            surface="zusd",
            updated_at_ms=1_778_730_001_000,
        )
    except ValueError as exc:
        assert "wallet sync state hash mismatch" in str(exc)
    else:
        raise AssertionError("tampered sync state was accepted")


def test_wallet_sync_state_rejects_valid_higher_current_state_rollback(tmp_path: Path) -> None:
    headers_dir, bodies_dir, checkpoints_dir, registry_path, envelope_paths = _write_fixture_files(tmp_path)
    bundle = build_browser_bundle_from_files(
        headers_dir=headers_dir,
        bodies_dir=bodies_dir,
        checkpoints_dir=checkpoints_dir,
        registry_path=registry_path,
        envelope_paths=envelope_paths,
        from_height=1,
        to_height=2,
    )
    current_higher = wallet_sync_state_v0(
        current_state=None,
        checkpoint_bundle=bundle,
        surface="zusd",
        updated_at_ms=1_778_730_000_000,
    )
    current_higher_body = {key: current_higher[key] for key in current_higher if key != "state_hash"}
    current_higher_body["height"] = 3
    current_higher = {
        **current_higher_body,
        "state_hash": hash_v0("wallet_sync_state_v0", current_higher_body),
    }

    try:
        wallet_sync_state_v0(
            current_state=current_higher,
            checkpoint_bundle=bundle,
            surface="zusd",
            updated_at_ms=1_778_730_001_000,
        )
    except ValueError as exc:
        assert "rollback rejected" in str(exc)
    else:
        raise AssertionError("rollback was accepted")


def test_build_browser_bundle_cli_writes_bundle(tmp_path: Path, capsys) -> None:
    headers_dir, bodies_dir, checkpoints_dir, registry_path, envelope_paths = _write_fixture_files(tmp_path)
    out = tmp_path / "browser-bundle.json"

    code = main(
        [
            "--headers-dir",
            str(headers_dir),
            "--bodies-dir",
            str(bodies_dir),
            "--checkpoints-dir",
            str(checkpoints_dir),
            "--registry",
            str(registry_path),
            "--envelope",
            str(envelope_paths[0]),
            "--envelope",
            str(envelope_paths[1]),
            "--from-height",
            "1",
            "--to-height",
            "2",
            "--out",
            str(out),
        ]
    )

    report = json.loads(capsys.readouterr().out)
    assert code == 0
    assert report["ok"] is True
    assert report["status"] == "structural_diagnostic_packaged"
    assert out.is_file()
    bundle = json.loads(out.read_text(encoding="utf-8"))
    assert bundle["bundle_hash"] == report["bundle_hash"]
    validate_browser_checkpoint_bundle_v0(bundle)


def test_browser_sdk_verifies_python_built_bundle_hashes(tmp_path: Path) -> None:
    headers_dir, bodies_dir, checkpoints_dir, registry_path, envelope_paths = _write_fixture_files(tmp_path)
    out = tmp_path / "browser-bundle.json"
    bundle = build_browser_bundle_from_files(
        headers_dir=headers_dir,
        bodies_dir=bodies_dir,
        checkpoints_dir=checkpoints_dir,
        registry_path=registry_path,
        envelope_paths=envelope_paths,
        from_height=1,
        to_height=2,
    )
    out.write_text(json.dumps(bundle, indent=2, sort_keys=True), encoding="utf-8")

    sdk_uri = (ROOT / "tools" / "dex-ui" / "src" / "sdk" / "zenoProofClient.js").resolve().as_uri()
    script = f"""
import fs from 'node:fs';
import {{ advanceWalletSyncStateV0, verifyBrowserCheckpointBundleV0 }} from {json.dumps(sdk_uri)};

const bundle = JSON.parse(fs.readFileSync({json.dumps(str(out))}, 'utf8'));
const report = await verifyBrowserCheckpointBundleV0(bundle);
if (!report.ok) {{
  throw new Error(report.gaps.join('; '));
}}
if (report.bundle_hash !== bundle.bundle_hash) {{
  throw new Error('bundle hash mismatch across Python and browser SDK');
}}
if (report.checkpoint_hash !== bundle.verification_summary.checkpoint_hash) {{
  throw new Error('checkpoint hash mismatch across Python and browser SDK');
}}
const sync = await advanceWalletSyncStateV0({{
  bundle,
  surface: 'zusd',
  updatedAtMs: 1778730000000,
}});
if (!sync.ok) {{
  throw new Error(sync.gaps.join('; '));
}}
console.log(JSON.stringify({{
  ok: true,
  bundle_hash: report.bundle_hash,
  checkpoint_hash: report.checkpoint_hash,
  state_hash: sync.state.state_hash,
}}));
"""
    proc = subprocess.run(
        ["node", "--input-type=module", "-e", script],
        cwd=ROOT / "tools" / "dex-ui",
        text=True,
        capture_output=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    payload = json.loads(proc.stdout)
    assert payload["ok"] is True
    assert payload["bundle_hash"] == bundle["bundle_hash"]
    assert payload["checkpoint_hash"] == bundle["verification_summary"]["checkpoint_hash"]
    assert payload["state_hash"].startswith("0x")


def test_browser_sdk_independent_bls_rejects_signatures_for_wrong_checkpoint(tmp_path: Path) -> None:
    headers_dir, bodies_dir, checkpoints_dir, registry_path, envelope_paths = _write_fixture_files(tmp_path)
    out = tmp_path / "browser-bundle-wrong-payload.json"
    bundle = build_browser_bundle_from_files(
        headers_dir=headers_dir,
        bodies_dir=bodies_dir,
        checkpoints_dir=checkpoints_dir,
        registry_path=registry_path,
        envelope_paths=envelope_paths,
        from_height=1,
        to_height=2,
    )
    wrong_payload_hash = "0x" + "fe" * 32
    bundle["signature_envelopes"] = [
        build_bls_signed_artifact_envelope_v0(
            payload_kind="checkpoint",
            payload_hash=wrong_payload_hash,
            signer_id="release-watcher-a",
            key_id="release-bls-key-a",
            private_key_hex=TEST_BLS_PRIVATE_KEY_A,
        ),
        build_bls_signed_artifact_envelope_v0(
            payload_kind="checkpoint",
            payload_hash=wrong_payload_hash,
            signer_id="release-watcher-b",
            key_id="release-bls-key-b",
            private_key_hex=TEST_BLS_PRIVATE_KEY_B,
        ),
    ]
    out.write_text(json.dumps(bundle, indent=2, sort_keys=True), encoding="utf-8")

    sdk_uri = (ROOT / "tools" / "dex-ui" / "src" / "sdk" / "zenoProofClient.js").resolve().as_uri()
    script = f"""
import fs from 'node:fs';
import {{ hashV0, verifyBrowserCheckpointBundleV0 }} from {json.dumps(sdk_uri)};

const bundle = JSON.parse(fs.readFileSync({json.dumps(str(out))}, 'utf8'));
const oldHash = bundle.bundle_hash;
delete bundle.bundle_hash;
bundle.bundle_hash = await hashV0('browser_checkpoint_bundle_v0', bundle);
if (bundle.bundle_hash === oldHash) {{
  throw new Error('test fixture did not perturb bundle hash');
}}
const report = await verifyBrowserCheckpointBundleV0(bundle, {{ requireIndependentBls: true }});
console.log(JSON.stringify(report));
"""
    proc = subprocess.run(
        ["node", "--input-type=module", "-e", script],
        cwd=ROOT / "tools" / "dex-ui",
        text=True,
        capture_output=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    report = json.loads(proc.stdout)
    assert report["ok"] is False
    assert "payload_hash" in "\n".join(report["gaps"])


def test_zenoctl_light_client_build_browser_bundle_dry_run(capsys) -> None:
    from tools import zenoctl

    rc = zenoctl.main(
        [
            "light-client",
            "build-browser-bundle",
            "--headers-dir",
            "/tmp/headers",
            "--bodies-dir",
            "/tmp/bodies",
            "--checkpoints-dir",
            "/tmp/checkpoints",
            "--registry",
            "/tmp/registry.json",
            "--envelope",
            "/tmp/a.sig.json",
            "--envelope",
            "/tmp/b.sig.json",
            "--from-height",
            "1",
            "--to-height",
            "10",
            "--trusted-prev-header-hash",
            ZERO_ROOT,
            "--out",
            "/tmp/browser-bundle.json",
            "--dry-run",
        ]
    )

    assert rc == 0
    output = capsys.readouterr().out
    assert "tools/build_zeno_sdk_browser_bundle.py" in output
    assert "--out /tmp/browser-bundle.json" in output


def test_browser_sdk_node_tests_pass() -> None:
    proc = subprocess.run(
        ["npm", "run", "test:sdk"],
        cwd=ROOT / "tools" / "dex-ui",
        text=True,
        capture_output=True,
        check=False,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
