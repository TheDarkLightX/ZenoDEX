from __future__ import annotations

import json
import subprocess
from pathlib import Path

import pytest

from tools import plan_zkpf_reproof as planner

REPO_ROOT = Path(__file__).resolve().parents[1]
GRAPH_PATH = REPO_ROOT / "config/proof_profiles/zkpf_reproof_graph_v1.json"


def _graph() -> planner.Graph:
    return planner.parse_graph(GRAPH_PATH.read_bytes())


def test_graph_is_canonical_acyclic_and_bounded() -> None:
    parsed = _graph()
    assert len(parsed.stages) == 18
    assert parsed.canonical_bytes == GRAPH_PATH.read_bytes()
    assert len(parsed.digest) == 64


def test_leaf_change_plans_exact_transitive_chain() -> None:
    plan = planner.plan_reproof(
        _graph(),
        ["zk/zrpf_risc0/spot_value_leaf_v6_shared/src/lib.rs"],
    )
    assert [row["stage_id"] for row in plan["tasks"]] == [
        "spot_value_leaf_v6",
        "spot_value_aggregate_l1_v6",
        "spot_value_aggregate_l2_v6",
        "spot_settlement_v6",
        "spot_settlement_v7",
        "zrpf_host_verifiers",
        "release_closure_v7",
        "firecracker_authority_v7",
        "atomic_operational_join_v7",
        "production_qualification",
    ]
    assert plan["direct_invalidations"] == [
        {
            "stage_id": "spot_value_leaf_v6",
            "matched_paths": [
                "zk/zrpf_risc0/spot_value_leaf_v6_shared/src/lib.rs"
            ],
        }
    ]


def test_recursive_glob_with_wildcard_prefix_matches() -> None:
    assert planner._matches("zk/demo/prover/engine.rs", "zk/**/prover/**")
    assert planner._matches(
        "zk/zrpf_risc0/methods/spot_value_leaf_v6/src/main.rs",
        "zk/zrpf_risc0/methods/**",
    )


def test_unrelated_documentation_change_produces_no_tasks() -> None:
    plan = planner.plan_reproof(_graph(), ["docs/unrelated.md"])
    assert plan["tasks"] == []
    assert plan["execution_waves"] == []
    assert len(plan["unaffected_stages"]) == len(_graph().stages)


def test_plan_is_independent_of_changed_path_input_order() -> None:
    left = planner.plan_reproof(
        _graph(),
        [
            "zk/zrpf_protocol/protocol/src/full_blob_da_v1/policy.rs",
            "src/integration/_zrpf_spot_v7_firecracker_authority.py",
        ],
    )
    right = planner.plan_reproof(
        _graph(),
        list(reversed(left["changed_paths"])),
    )
    assert planner.canonical_json_bytes(left) == planner.canonical_json_bytes(right)


def test_planned_stages_are_explicitly_blocked() -> None:
    plan = planner.plan_reproof(
        _graph(),
        ["src/integration/zrpf_spot_v7_checkpoint_finality_adapter.py"],
    )
    task = next(
        row
        for row in plan["tasks"]
        if row["stage_id"] == "checkpoint_finality_adapter_v2"
    )
    assert task["implementation_status"] == "planned"
    assert task["blocked_by_missing_implementation"] is True
    assert all(value is False for value in task["authority"].values())


def test_cycle_and_unknown_dependency_reject() -> None:
    value = json.loads(GRAPH_PATH.read_text(encoding="ascii"))
    value["stages"][0]["depends_on"] = [value["stages"][0]["id"]]
    with pytest.raises(planner.ReproofPlanError, match="dependency set"):
        planner.parse_graph(planner.canonical_json_bytes(value))

    value = json.loads(GRAPH_PATH.read_text(encoding="ascii"))
    value["stages"][0]["depends_on"] = ["missing"]
    with pytest.raises(planner.ReproofPlanError, match="dependency set"):
        planner.parse_graph(planner.canonical_json_bytes(value))


def test_duplicate_noncanonical_and_unsafe_inputs_reject() -> None:
    with pytest.raises(planner.ReproofPlanError, match="duplicate JSON key"):
        planner.parse_graph(b'{"schema":"a","schema":"b"}\n')
    with pytest.raises(planner.ReproofPlanError, match="not canonical"):
        planner.parse_graph(
            json.dumps(
                json.loads(GRAPH_PATH.read_text(encoding="ascii")),
                indent=2,
            ).encode("ascii")
        )
    with pytest.raises(planner.ReproofPlanError, match="safe repository-relative"):
        planner.plan_reproof(_graph(), ["../escape"])


def test_task_bundle_is_content_addressed_and_publish_once(tmp_path: Path) -> None:
    plan = planner.plan_reproof(
        _graph(),
        ["zk/zrpf_risc0/spot_value_leaf_v6_shared/src/lib.rs"],
    )
    output = tmp_path / "tasks"
    planner._write_tasks(output, plan)
    index = json.loads((output / "index.json").read_text(encoding="ascii"))
    assert len(index["tasks"]) == len(plan["tasks"])
    assert all((output / row["file"]).is_file() for row in index["tasks"])
    with pytest.raises(planner.ReproofPlanError, match="begin absent"):
        planner._write_tasks(output, plan)


def test_git_diff_mode_uses_exact_merge_base_range(tmp_path: Path) -> None:
    subprocess.run(["git", "init", "-q"], cwd=tmp_path, check=True)
    subprocess.run(
        ["git", "config", "user.email", "test@example.com"],
        cwd=tmp_path,
        check=True,
    )
    subprocess.run(
        ["git", "config", "user.name", "test"],
        cwd=tmp_path,
        check=True,
    )
    source = tmp_path / "src" / "a"
    source.mkdir(parents=True)
    (source / "one.rs").write_text("one\n", encoding="utf-8")
    subprocess.run(["git", "add", "."], cwd=tmp_path, check=True)
    subprocess.run(["git", "commit", "-qm", "base"], cwd=tmp_path, check=True)
    base = subprocess.check_output(
        ["git", "rev-parse", "HEAD"],
        cwd=tmp_path,
        text=True,
    ).strip()
    (source / "one.rs").write_text("two\n", encoding="utf-8")
    subprocess.run(["git", "commit", "-qam", "head"], cwd=tmp_path, check=True)
    head = subprocess.check_output(
        ["git", "rev-parse", "HEAD"],
        cwd=tmp_path,
        text=True,
    ).strip()
    assert planner._git_changed_paths(tmp_path, base, head) == ("src/a/one.rs",)
