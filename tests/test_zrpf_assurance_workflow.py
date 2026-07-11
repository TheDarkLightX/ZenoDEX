from __future__ import annotations

from pathlib import Path

import yaml

ROOT = Path(__file__).resolve().parents[1]
WORKFLOW = ROOT / ".github/workflows/zrpf-assurance.yml"
DOCKERFILE = ROOT / ".docker/zrpf-assurance.Dockerfile"


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
    tag_check = steps["Verify durable source-anchor tags"]["run"]
    assert "zrpf-v3-source-anchor-20260710" in tag_check
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
    broad_cargo_mount = '"${HOME}/.cargo:/home/' + 'zrpf/.cargo:ro"'
    exact_registry_mount = (
        '"${HOME}/.cargo/registry:/home/' + 'zrpf/.cargo/registry:ro"'
    )
    assert broad_cargo_mount not in replay_command
    assert '"${HOME}/.risc0:/risc0:ro"' not in replay_command
    assert exact_registry_mount in replay_command
    assert "v1.94.1-rust-x86_64-unknown-linux-gnu:/risc0/toolchains/" in replay_command
    python_assurance = steps["Run Python and evidence assurance"]["run"]
    rust_assurance = steps["Run Rust protocol and verifier assurance"]["run"]
    assert "tools/check_zrpf_v1_leaf_adapter_source_policy.py" in python_assurance
    assert "tests/test_check_zrpf_v1_leaf_adapter_source_policy.py" in python_assurance
    assert "tools/check_recursive_stark_cbc_spec.py" in python_assurance
    assert "tests/test_check_recursive_stark_cbc_spec.py" in python_assurance
    assert "tools/check_zrpf_v3_firecracker_replay_profile.py" in python_assurance
    assert "tools/zrpf_v3_firecracker_host_probe.py" in python_assurance
    assert "tests/test_check_zrpf_v3_firecracker_replay_profile.py" in python_assurance
    assert "tests/test_zrpf_v3_firecracker_profile_boundary_atlas.py" in (
        python_assurance
    )
    assert "tests/test_zrpf_v3_firecracker_host_probe.py" in python_assurance
    assert "python3 -I tools/check_zrpf_v3_firecracker_replay_profile.py" in (
        python_assurance
    )
    assert "check_zrpf_v3_firecracker_replay_profile.py --probe-host" not in raw
    assert "--manifest-path zk/recursive_stark_v2_risc0/Cargo.toml" in rust_assurance
    assert rust_assurance.count("-p zenodex-zrpf-risc0-harness") == 2
    assert rust_assurance.count('"${pinned_bin}/cargo-clippy" clippy') == 3
    assert '"${pinned_bin}/cargo" clippy' not in rust_assurance
    assert "ZENODEX_RUN_NATIVE_ZRPF_REPLAY" not in raw
    assert steps["Checkout full source history"]["uses"] == (
        "actions/checkout@df4cb1c069e1874edd31b4311f1884172cec0e10"
    )
    assert steps["Set up Python"]["uses"] == (
        "actions/setup-python@ece7cb06caefa5fff74198d8649806c4678c61a1"
    )
    assert steps["Upload ZRPF assurance report"]["uses"] == (
        "actions/upload-artifact@330a01c490aca151604b8cf639adc76d48f6c5d4"
    )


def test_zrpf_assurance_container_is_digest_pinned_and_nonroot() -> None:
    raw = DOCKERFILE.read_text(encoding="utf-8")

    assert raw.startswith(
        "FROM ubuntu@sha256:"
        "4fbb8e6a8395de5a7550b33509421a2bafbc0aab6c06ba2cef9ebffbc7092d90\n"
    )
    assert "USER 10001:10001" in raw
    assert "COPY " not in raw
    assert "ADD " not in raw
