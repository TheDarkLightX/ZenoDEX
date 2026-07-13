from __future__ import annotations

import re
import tomllib
from pathlib import Path

import yaml

ROOT = Path(__file__).resolve().parents[1]
WORKFLOW = ROOT / ".github/workflows/zrpf-assurance.yml"
DOCKERFILE = ROOT / ".docker/zrpf-assurance.Dockerfile"
ZRPF_WORKSPACE = ROOT / "zk/zrpf_risc0/Cargo.toml"


def _zrpf_workspace_packages() -> tuple[set[str], set[str]]:
    workspace = tomllib.loads(ZRPF_WORKSPACE.read_text(encoding="utf-8"))
    host_packages: set[str] = set()
    guest_packages: set[str] = set()
    for member in workspace["workspace"]["members"]:
        manifest = ZRPF_WORKSPACE.parent / member / "Cargo.toml"
        package = tomllib.loads(manifest.read_text(encoding="utf-8"))["package"]["name"]
        if member.startswith("methods/"):
            guest_packages.add(package)
        else:
            host_packages.add(package)
    return host_packages, guest_packages


def _cargo_package_args(command: str) -> list[str]:
    return re.findall(r"(?:^|\s)-p\s+([A-Za-z0-9_-]+)(?=\s|$)", command)


def test_zrpf_assurance_workflow_is_required_lane_ready() -> None:
    raw = WORKFLOW.read_text(encoding="utf-8")
    document = yaml.safe_load(raw)
    workflow_events = document[True]
    job = document["jobs"]["zrpf-assurance"]
    steps = {step["name"]: step for step in job["steps"]}
    replay_command = steps["Run required source-built replay without network"]["run"]

    assert document["permissions"] == {"contents": "read"}
    assert document["jobs"].keys() == {"zrpf-assurance"}
    assert workflow_events["pull_request"] is None
    assert "paths" not in workflow_events
    assert "pull_request_target" not in raw
    assert "secrets." not in raw
    assert steps["Checkout full source history"]["with"] == {
        "fetch-depth": 0,
        "persist-credentials": False,
    }
    assert steps["Set up Node for browser-verifier assurance"]["uses"] == (
        "actions/setup-node@48b55a011bda9f5d6aeb4c2d9c7362e8dae4041e"
    )
    assert steps["Set up Node for browser-verifier assurance"]["with"] == {
        "node-version": "22",
        "cache": "npm",
        "cache-dependency-path": "tools/dex-ui/package-lock.json",
    }
    assert steps["Install lockfile-bound browser-verifier dependencies"] == {
        "name": "Install lockfile-bound browser-verifier dependencies",
        "working-directory": "tools/dex-ui",
        "run": "npm ci --ignore-scripts --no-audit --no-fund",
    }
    tag_check = steps["Verify durable source-anchor tags"]["run"]
    assert "zrpf-v3-source-anchor-20260711" in tag_check
    assert "zrpf-v3-source-anchor-v7-20260712" in tag_check
    assert "zrpf-v1-retained-source-anchor-20260710" in tag_check
    assert "--network none" in replay_command
    assert "--read-only" in replay_command
    assert "--cap-drop ALL" in replay_command
    assert "--security-opt no-new-privileges" in replay_command
    assert "--pids-limit 512" in replay_command
    assert "--tmpfs /out:rw,exec,nosuid,nodev,size=6g,mode=1777" in replay_command
    assert "cp -R" not in replay_command
    assert "export GIT_CONFIG_NOSYSTEM=1" in replay_command
    assert "export HOME=/out/private/git-home" in replay_command
    assert "git config --global --add safe.directory /input\n" in replay_command
    assert "git config --global --add safe.directory /input/.git" in replay_command
    assert "git clone --no-checkout --no-hardlinks /input" in replay_command
    assert "--no-checkout --no-hardlinks /input /out/private/repo" in replay_command
    assert 'checkout --detach "${source_head}"' in replay_command
    assert "--live" in replay_command
    assert 'live_report="internal/zrpf-ci-live-replay.pending.json"' in replay_command
    assert '\' | tee "${live_report}"' in replay_command
    assert 'mv "${live_report}" internal/zrpf-ci-live-replay.json' in replay_command
    assert "json.loads(report_path.read_text" in replay_command
    assert 'value.get("ok") is not True' in replay_command
    broad_cargo_mount = '"${HOME}/.cargo:/home/' + 'zrpf/.cargo:ro"'
    exact_registry_mount = '"${HOME}/.cargo/registry:/home/' + 'zrpf/.cargo/registry:ro"'
    assert broad_cargo_mount not in replay_command
    assert '"${HOME}/.risc0:/risc0:ro"' not in replay_command
    assert exact_registry_mount in replay_command
    assert "v1.94.1-rust-x86_64-unknown-linux-gnu:/risc0/toolchains/" in replay_command
    python_assurance = steps["Run Python and evidence assurance"]["run"]
    rust_assurance = steps["Run Rust protocol and verifier assurance"]["run"]
    active_replay = steps[
        "Build governed host verifiers and cryptographically replay retained roots"
    ]["run"]
    current_guest_build = steps["Build pinned current RISC0 guests"]["run"]
    guest_assurance = steps["Check every ZRPF guest on the zkVM target"]["run"]
    cargo_acquisition = steps["Acquire lockfile-bound Cargo sources"]["run"]
    assert "--manifest-path zk/state_proof_risc0/Cargo.toml" in cargo_acquisition
    assert "tools/check_zrpf_v1_leaf_adapter_source_policy.py" in python_assurance
    assert "tests/test_check_zrpf_v1_leaf_adapter_source_policy.py" in python_assurance
    assert "tools/check_risc0_recursive_rebuild_evidence.py" in python_assurance
    assert "tests/test_check_risc0_recursive_rebuild_evidence.py" in python_assurance
    assert "tools/check_risc0_recursive_live_replay.py" in python_assurance
    assert "tools/check_risc0_recursive_live_replay_evidence.py" in python_assurance
    assert "tools/risc0_recursive_live_replay_support.py" in python_assurance
    assert "tests/test_check_risc0_recursive_live_replay.py" in python_assurance
    assert "tests/test_check_risc0_recursive_live_replay_evidence.py" in python_assurance
    assert "python3 tools/check_risc0_recursive_live_replay_evidence.py --json" in (
        python_assurance
    )
    assert (
        "--artifact docs/research/RISC0_RECURSIVE_V1_LIVE_REPLAY_EVIDENCE_20260712.json"
        in python_assurance
    )
    assert "tools/check_recursive_stark_cbc_spec.py" in python_assurance
    assert "tests/test_check_recursive_stark_cbc_spec.py" in python_assurance
    assert "tools/check_zrpf_semantic_epoch_v1_local_evidence.py" in python_assurance
    assert "tests/test_build_zrpf_semantic_epoch_v1_local_evidence.py" in python_assurance
    assert "tests/test_check_zrpf_semantic_epoch_v1_local_evidence.py" in python_assurance
    assert "tests/test_zrpf_semantic_guest_source_contract.py" in python_assurance
    assert "tools/check_zrpf_v4_spot_value_leaf_local_evidence.py" in python_assurance
    assert "tools/zrpf_v4_spot_value_leaf_evidence_support.py" in python_assurance
    assert "tools/zrpf_evidence_boundary_concolic.py" in python_assurance
    assert "tests/test_check_zrpf_v4_spot_value_leaf_local_evidence.py" in python_assurance
    assert "tools/check_zrpf_value_aggregate_v5_build_record.py" in python_assurance
    assert "tests/test_check_zrpf_value_aggregate_v5_build_record.py" in python_assurance
    assert "tests/test_zrpf_evidence_boundary_concolic.py" in python_assurance
    ruff_assurance, after_ruff = python_assurance.split(
        "\nmypy --follow-imports=skip \\\n",
        maxsplit=1,
    )
    mypy_assurance, after_mypy = after_ruff.split("\npytest -q \\\n", maxsplit=1)
    pytest_assurance, _ = after_mypy.split(
        "\npython3 tools/check_zrpf_v1_leaf_adapter_source_policy.py",
        maxsplit=1,
    )
    for required_path in (
        "src/core/recursive_stark_admission.py",
        "src/integration/_recursive_stark_admission_store_engine.py",
        "src/integration/_recursive_stark_admission_store_hashes.py",
        "src/integration/_recursive_stark_admission_store_history.py",
        "src/integration/_recursive_stark_admission_store_schema.py",
        "src/integration/recursive_stark_admission_store.py",
        "src/integration/recursive_stark_admission_store_types.py",
        "src/integration/recursive_stark_replay_manifest.py",
        "src/integration/recursive_stark_verifier_adapter.py",
        "src/integration/zeno_ledger_authenticated_proof_verification_v1.py",
        "src/integration/zeno_ledger_watcher.py",
        "src/integration/zeno_sdk_browser_bundle_v0.py",
        "tools/build_zeno_sdk_browser_bundle.py",
        "tools/check_zeno_ledger_light_client_checkpoint.py",
        "tools/zeno_ledger_verify.py",
    ):
        assert required_path in ruff_assurance
        assert required_path in mypy_assurance
    for required_path in (
        "tests/core/test_recursive_stark_exact_once_admission.py",
        "tests/integration/test_recursive_stark_admission_authority_boundary.py",
        "tests/integration/test_recursive_stark_durable_admission_store.py",
        "tests/integration/test_recursive_stark_replay_manifest.py",
        "tests/integration/test_recursive_stark_verifier_adapter.py",
        "tests/integration/test_zeno_ledger_authenticated_proof_verification_v1.py",
        "tests/integration/test_zeno_ledger_proof_required_authority_wiring_v1.py",
    ):
        assert required_path in ruff_assurance
        assert required_path in mypy_assurance
        assert required_path in pytest_assurance
    for required_path in (
        "tests/integration/test_zeno_ledger_replay_bound_verify.py",
        "tests/test_check_zeno_ledger_light_client_checkpoint.py",
        "tests/test_zeno_sdk_browser_bundle.py",
    ):
        assert required_path in ruff_assurance
        assert required_path in pytest_assurance
    for required_path in (
        "tools/zrpf_v3_source_closure.py",
        "tests/test_zrpf_v3_source_closure.py",
    ):
        assert required_path in ruff_assurance
        assert required_path in mypy_assurance
    assert "tools/check_risc0_recursive_rebuild_evidence.py" in ruff_assurance
    assert "tools/check_risc0_recursive_rebuild_evidence.py" in mypy_assurance
    assert "tests/test_check_risc0_recursive_rebuild_evidence.py" in ruff_assurance
    assert "tests/test_check_risc0_recursive_rebuild_evidence.py" in pytest_assurance
    for required_path in (
        "tools/check_risc0_recursive_active_reproof_v3.py",
        "tools/build_risc0_recursive_active_reproof_reference_v3.py",
    ):
        assert required_path in ruff_assurance
        assert required_path in mypy_assurance
    assert "tests/test_check_risc0_recursive_active_reproof_v3.py" in ruff_assurance
    assert "tests/test_check_risc0_recursive_active_reproof_v3.py" in pytest_assurance
    assert "python3 tools/check_risc0_recursive_active_reproof_v3.py" in python_assurance
    assert "zrpf-v3-firecracker-elf-source-v2-20260712" in raw
    assert "25032924eb4fca7f156a9ec4eedd39afeade9623" in raw
    assert "tools/check_zrpf_v3_firecracker_direct_replay_evidence.py" in (python_assurance)
    assert "tests/test_check_zrpf_v3_firecracker_direct_replay_evidence.py" in (python_assurance)
    assert "tests/test_check_zrpf_v3_firecracker_guest_elf.py" in python_assurance
    assert "tools/check_zrpf_v3_firecracker_guest_elf.py" in python_assurance
    assert "tools/check_zrpf_v3_firecracker_replay_profile.py" in python_assurance
    assert "tools/check_zrpf_v3_firecracker_protocol_binding.py" in python_assurance
    assert "tools/check_zrpf_v3_firecracker_runtime_artifacts.py" in python_assurance
    assert "tools/check_zrpf_v3_firecracker_launch_preflight.py" in python_assurance
    assert "tools/zrpf_v3_firecracker_host_probe.py" in python_assurance
    assert "tests/test_check_zrpf_v3_firecracker_replay_profile.py" in python_assurance
    assert "tests/test_zrpf_v3_firecracker_profile_boundary_atlas.py" in (python_assurance)
    assert "tests/test_zrpf_v3_firecracker_host_probe.py" in python_assurance
    assert "tests/test_check_zrpf_v3_firecracker_protocol_binding.py" in python_assurance
    assert "tests/test_check_zrpf_v3_firecracker_runtime_artifacts.py" in python_assurance
    assert "tests/test_check_zrpf_v3_firecracker_launch_preflight.py" in python_assurance
    assert "tests/test_zrpf_v3_firecracker_launch_boundary_atlas.py" in python_assurance
    assert "python3 -I tools/check_zrpf_v3_firecracker_replay_profile.py" in (python_assurance)
    assert "python3 -I tools/check_zrpf_v3_firecracker_protocol_binding.py" in (python_assurance)
    assert "python3 -I tools/check_zrpf_v3_firecracker_direct_replay_evidence.py" in (
        python_assurance
    )
    assert "check_zrpf_v3_firecracker_runtime_artifacts.py" in python_assurance
    assert "--evidence-date" not in python_assurance
    assert "date -u" not in python_assurance
    assert "--current-release-date" not in python_assurance
    assert "--require-current-runtime-eligible" not in python_assurance
    assert "bash -n tools/build_zrpf_v3_firecracker_guest_images.sh" in (python_assurance)
    assert "check_zrpf_v3_firecracker_replay_profile.py --probe-host" not in raw
    assert "--manifest-path zk/recursive_stark_v2_risc0/Cargo.toml" in rust_assurance
    assert "--manifest-path zk/recursive_stark_v2_active_reproof_risc0/Cargo.toml" in rust_assurance
    assert "--manifest-path zk/state_proof_risc0/Cargo.toml" in rust_assurance
    assert rust_assurance.count("--manifest-path zk/state_proof_risc0/Cargo.toml") == 3
    assert rust_assurance.count("-p tau-state-proof-risc0-cli --all-targets") == 2
    assert rust_assurance.count("--locked --offline -p tau-state-proof-risc0-cli") == 2
    assert rust_assurance.count("-p zenodex-zrpf-risc0-harness") == 2
    assert rust_assurance.count("-p zenodex-zrpf-risc0-semantic-shared") == 4
    assert rust_assurance.count("-p zenodex-zrpf-risc0-value-node-shared") == 2
    assert rust_assurance.count("-p zenodex-zrpf-risc0-value-aggregate-shared") == 2
    assert rust_assurance.count("-p zenodex-zrpf-risc0-value-aggregate-l2-policy") == 2
    assert rust_assurance.count("-p zenodex-zrpf-risc0-value-aggregate-root-policy") == 2
    assert rust_assurance.count("-p zenodex-zrpf-risc0-methods") == 2
    assert "--locked --all-targets" in rust_assurance
    assert rust_assurance.count("--no-default-features --test semantic_v2") == 2
    assert rust_assurance.count('"${pinned_bin}/cargo-clippy" clippy') == 6
    assert '"${pinned_bin}/cargo" clippy' not in rust_assurance
    host_packages, guest_packages = _zrpf_workspace_packages()
    host_package_args = _cargo_package_args(rust_assurance)
    guest_package_args = _cargo_package_args(guest_assurance)
    for package in host_packages:
        assert host_package_args.count(package) >= 2, package
        assert package not in guest_package_args
    for package in guest_packages:
        assert package not in host_package_args
        assert guest_package_args.count(package) == 1, package
    assert "RISC0_SKIP_BUILD=1" in guest_assurance
    assert "CARGO_ENCODED_RUSTFLAGS" in guest_assurance
    assert 'getrandom_backend="custom"' in guest_assurance
    assert '"${pinned_bin}/cargo" check' in guest_assurance
    assert "cargo test" not in guest_assurance
    assert "cargo clippy" not in guest_assurance
    assert "--locked --offline" in guest_assurance
    assert "--target riscv32im-risc0-zkvm-elf" in guest_assurance
    assert '--target-dir "${RUNNER_TEMP}/zrpf-guest-check"' in guest_assurance
    assert "zenodex-zrpf-risc0-semantic-epoch" in guest_packages
    assert "export RISC0_SKIP_BUILD=1" in active_replay
    assert "unset RISC0_SKIP_BUILD" not in active_replay
    assert "--manifest-path zk/state_proof_risc0/Cargo.toml" not in active_replay
    assert "--manifest-path zk/recursive_stark_v2_active_reproof_risc0/Cargo.toml" in (
        active_replay
    )
    assert "--bin verify_recursive_v1_root" in active_replay
    assert "--bin verify_recursive_v2_pair" in active_replay
    assert "v1-root.verify.request.json" in active_replay
    assert "v1-root.active-verifier.json" in active_replay
    assert "RISC0_DEV_MODE=1" in active_replay
    assert "v1-root.seal-word-1-xor-lsb.proof.json" in active_replay
    assert 'metadata["proof"]["meta"]["public_policy_hash"]' in active_replay
    assert 'expectations["recursive_expectations"]["public_policy_hash"]' in active_replay
    assert "child_bytes[0] ^= 1" in active_replay
    assert "v1-disclosure.verify.request.json" in active_replay
    assert 'unknown["recursive_input"]["unrecognized_but_canonical"]' in active_replay
    assert "v1-unknown.verify.request.json" in active_replay
    assert "v2-inner.proof.json" in active_replay
    assert "v2-root.proof.json" in active_replay
    assert "v2-root.seal-word-1-xor-lsb.proof.json" in active_replay
    assert "v2-pair.verify.json" in active_replay
    assert "unset RISC0_SKIP_BUILD" in current_guest_build
    assert "RISC0_SKIP_BUILD=1" not in current_guest_build
    assert 'CARGO_TARGET_DIR="${RUNNER_TEMP}/zrpf-current-guest-build"' in current_guest_build
    assert "--frozen --offline --release" in current_guest_build
    assert "-p zenodex-zrpf-risc0-methods" in current_guest_build
    assert "ZENODEX_RUN_NATIVE_ZRPF_REPLAY" not in raw
    assert steps["Checkout full source history"]["uses"] == (
        "actions/checkout@df4cb1c069e1874edd31b4311f1884172cec0e10"
    )
    assert steps["Set up Python"]["uses"] == (
        "actions/setup-python@ece7cb06caefa5fff74198d8649806c4678c61a1"
    )
    initializer = steps["Initialize fail-closed ZRPF assurance report"]["run"]
    assert '"accepted":false' in initializer
    assert '"status":"not_run"' in initializer
    assert '"reason":"required_source_built_replay_did_not_complete"' in initializer
    assert "> internal/zrpf-ci-live-replay.json" in initializer
    assert steps["Upload ZRPF assurance report"]["uses"] == (
        "actions/upload-artifact@330a01c490aca151604b8cf639adc76d48f6c5d4"
    )
    assert steps["Upload ZRPF assurance report"]["if"] == "always()"
    assert steps["Upload ZRPF assurance report"]["with"]["if-no-files-found"] == "error"


def test_zrpf_assurance_container_is_digest_pinned_and_nonroot() -> None:
    raw = DOCKERFILE.read_text(encoding="utf-8")

    assert raw.startswith(
        "FROM ubuntu@sha256:4fbb8e6a8395de5a7550b33509421a2bafbc0aab6c06ba2cef9ebffbc7092d90\n"
    )
    assert "USER 10001:10001" in raw
    assert "COPY " not in raw
    assert "ADD " not in raw
