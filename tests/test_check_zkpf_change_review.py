from __future__ import annotations

import copy
import json
import subprocess
from pathlib import Path
from typing import cast

import pytest

from tools import check_zkpf_change_review as checker

REPO_ROOT = Path(__file__).resolve().parents[1]
CONFIG_PATH = REPO_ROOT / "config/proof_profiles/zkpf_change_classification_v1.json"


def _config() -> checker.ClassificationConfig:
    return checker.parse_config(CONFIG_PATH.read_bytes())


def _write(path: Path, raw: bytes = b"content\n") -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(raw)
    return path


def _valid_packet(
    config: checker.ClassificationConfig,
    change_set: checker.ChangeSet,
    requirements: checker.Requirements,
) -> dict[str, object]:
    value = checker.packet_skeleton(
        config=config,
        change_set=change_set,
        requirements=requirements,
    )
    value["confidence_bps"] = 9700
    value["invariant_ids"] = ["ZKPF.CHANGE.CLASSIFICATION.FAIL_CLOSED"]
    value["test_commands"] = [
        "python3 -m pytest -q tests/test_check_zkpf_change_review.py"
    ]
    value["negative_controls"] = [
        "missing or mismatched review packet rejects"
    ]
    value["paper_references"] = (
        ["docs/RISC0_CIRCUIT_QUALITY_CBC_SPEC.md"]
        if requirements.requires_paper_references
        else []
    )
    value["benchmark_evidence"] = (
        ["benchmarks/zkpf-change-review-baseline.json"]
        if requirements.requires_benchmark_evidence
        else []
    )
    value["divergence_records"] = [
        "review packet records intent but does not authenticate reviewer approval"
    ]
    value["review_state"] = "ready_for_human_review"
    return value


def _init_repo(root: Path) -> str:
    subprocess.run(["git", "init", "-q"], cwd=root, check=True)
    subprocess.run(
        ["git", "config", "user.email", "test@example.com"], cwd=root, check=True
    )
    subprocess.run(["git", "config", "user.name", "test"], cwd=root, check=True)
    subprocess.run(["git", "commit", "--allow-empty", "-qm", "base"], cwd=root, check=True)
    return subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=root, text=True
    ).strip()


def test_repository_config_is_canonical_and_classifies_gate() -> None:
    config = _config()
    assert config.raw == CONFIG_PATH.read_bytes()
    matched = [
        rule.id
        for rule in config.rules
        if any(
            checker._matches("tools/check_zkpf_change_review.py", pattern)
            for pattern in rule.globs
        )
    ]
    assert matched == ["change_review_gate"]


def test_recursive_glob_with_wildcard_prefix_matches() -> None:
    assert checker._matches("zk/demo/prover/engine.rs", "zk/**/prover/**")
    assert checker._matches(
        "zk/zrpf_risc0/methods/leaf/src/main.rs",
        "zk/zrpf_risc0/methods/**",
    )


def test_ordinary_change_needs_no_packet(tmp_path: Path) -> None:
    _write(tmp_path / "docs" / "ordinary.md")
    config = _config()
    change_set = checker.explicit_change_set(config, tmp_path, ["docs/ordinary.md"])
    report, accepted = checker.build_report(
        config=config,
        change_set=change_set,
        review_root=tmp_path / "reviews" / "zkpf",
        require_review=True,
    )
    assert accepted is True
    assert report["packet_required"] is False
    requirements_report = cast(dict[str, object], report["requirements"])
    assert requirements_report["affected_classes"] == []


def test_authority_change_requires_exact_packet(tmp_path: Path) -> None:
    _write(tmp_path / "tools" / "check_zkpf_change_review.py")
    config = _config()
    change_set = checker.explicit_change_set(
        config, tmp_path, ["tools/check_zkpf_change_review.py"]
    )
    classifications, requirements = checker.classify(config, change_set)
    assert classifications[0]["classes"] == ["authority"]
    review_root = tmp_path / "reviews" / "zkpf"
    report, accepted = checker.build_report(
        config=config,
        change_set=change_set,
        review_root=review_root,
        require_review=True,
    )
    assert accepted is False
    assert report["packet_error"] == "required review packet is absent"

    packet_path = checker.required_packet_path(review_root, change_set.digest)
    packet_path.parent.mkdir(parents=True)
    packet_path.write_bytes(
        checker.canonical_json_bytes(_valid_packet(config, change_set, requirements))
    )
    report, accepted = checker.build_report(
        config=config,
        change_set=change_set,
        review_root=review_root,
        require_review=True,
    )
    assert accepted is True
    assert report["packet_valid"] is True
    authority = cast(dict[str, bool], report["authority"])
    assert all(value is False for value in authority.values())


def test_draft_skeleton_and_substitutions_reject(tmp_path: Path) -> None:
    _write(tmp_path / "tools" / "check_zkpf_change_review.py")
    config = _config()
    change_set = checker.explicit_change_set(
        config, tmp_path, ["tools/check_zkpf_change_review.py"]
    )
    _, requirements = checker.classify(config, change_set)
    skeleton = checker.packet_skeleton(
        config=config, change_set=change_set, requirements=requirements
    )
    with pytest.raises(checker.ChangeReviewError, match="not ready"):
        checker.validate_packet(
            checker.canonical_json_bytes(skeleton),
            config=config,
            change_set=change_set,
            requirements=requirements,
        )

    baseline = _valid_packet(config, change_set, requirements)
    mutations = (
        ("config_sha256", "0" * 64, "config digest"),
        ("change_set_sha256", "0" * 64, "change-set digest"),
        ("changed_path_count", 99, "changed-path count"),
        ("confidence_bps", 9499, "confidence"),
        ("review_state", "approved", "not ready"),
    )
    for field, replacement, expected in mutations:
        candidate = copy.deepcopy(baseline)
        candidate[field] = replacement
        with pytest.raises(checker.ChangeReviewError, match=expected):
            checker.validate_packet(
                checker.canonical_json_bytes(candidate),
                config=config,
                change_set=change_set,
                requirements=requirements,
            )


def test_soundness_and_performance_require_union(tmp_path: Path) -> None:
    _write(tmp_path / "zk" / "demo" / "prover" / "engine.rs")
    _write(tmp_path / "zk" / "zrpf_protocol" / "protocol" / "src" / "lib.rs")
    config = _config()
    change_set = checker.explicit_change_set(
        config,
        tmp_path,
        [
            "zk/demo/prover/engine.rs",
            "zk/zrpf_protocol/protocol/src/lib.rs",
        ],
    )
    _, requirements = checker.classify(config, change_set)
    assert requirements.classes == ("performance", "soundness")
    assert requirements.requires_paper_references is True
    assert requirements.requires_negative_controls is True
    assert requirements.requires_benchmark_evidence is True
    assert set(requirements.reviewer_roles) == {
        "crypto_specialist",
        "math_reviewer",
        "performance_reviewer",
    }


def test_review_packet_path_is_excluded_in_explicit_and_git_modes(tmp_path: Path) -> None:
    config = _config()
    gate = _write(tmp_path / "tools" / "check_zkpf_change_review.py")
    first = checker.explicit_change_set(
        config, tmp_path, [gate.relative_to(tmp_path).as_posix()]
    )
    packet = _write(
        tmp_path / "reviews" / "zkpf" / f"{first.digest}.json",
        b"packet\n",
    )
    second = checker.explicit_change_set(
        config,
        tmp_path,
        [gate.relative_to(tmp_path).as_posix(), packet.relative_to(tmp_path).as_posix()],
    )
    assert first == second

    git_root = tmp_path / "git"
    git_root.mkdir()
    base = _init_repo(git_root)
    _write(git_root / "tools" / "check_zkpf_change_review.py")
    _write(git_root / "reviews" / "zkpf" / "placeholder.json")
    subprocess.run(["git", "add", "."], cwd=git_root, check=True)
    subprocess.run(["git", "commit", "-qm", "head"], cwd=git_root, check=True)
    head = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=git_root, text=True
    ).strip()
    change_set = checker.git_change_set(config, git_root, base, head)
    assert [(row.status, row.path) for row in change_set.paths] == [
        ("A", "tools/check_zkpf_change_review.py")
    ]


def test_duplicate_noncanonical_and_authority_promotion_reject(tmp_path: Path) -> None:
    with pytest.raises(checker.ChangeReviewError, match="duplicate JSON key"):
        checker.parse_config(b'{"schema":"a","schema":"b"}\n')
    with pytest.raises(checker.ChangeReviewError, match="not canonical"):
        checker.parse_config(
            json.dumps(
                json.loads(CONFIG_PATH.read_text(encoding="ascii")), indent=2
            ).encode("ascii")
        )

    _write(tmp_path / "tools" / "check_zkpf_change_review.py")
    config = _config()
    change_set = checker.explicit_change_set(
        config, tmp_path, ["tools/check_zkpf_change_review.py"]
    )
    _, requirements = checker.classify(config, change_set)
    packet = _valid_packet(config, change_set, requirements)
    authority = cast(dict[str, bool], packet["authority"])
    authority["production_authority"] = True
    with pytest.raises(checker.ChangeReviewError, match="promote authority"):
        checker.validate_packet(
            checker.canonical_json_bytes(packet),
            config=config,
            change_set=change_set,
            requirements=requirements,
        )


def test_git_rename_binds_deleted_and_added_paths(tmp_path: Path) -> None:
    _init_repo(tmp_path)
    old = _write(tmp_path / "src" / "integration" / "old_verifier.py")
    subprocess.run(["git", "add", "."], cwd=tmp_path, check=True)
    subprocess.run(["git", "commit", "-qm", "old"], cwd=tmp_path, check=True)
    base = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=tmp_path, text=True
    ).strip()
    new = tmp_path / "src" / "integration" / "new_verifier.py"
    old.rename(new)
    subprocess.run(["git", "add", "-A"], cwd=tmp_path, check=True)
    subprocess.run(["git", "commit", "-qm", "rename"], cwd=tmp_path, check=True)
    head = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=tmp_path, text=True
    ).strip()
    change_set = checker.git_change_set(_config(), tmp_path, base, head)
    assert [(row.status, row.path) for row in change_set.paths] == [
        ("A", "src/integration/new_verifier.py"),
        ("D", "src/integration/old_verifier.py"),
    ]


def test_changed_symlink_and_packet_symlink_reject(tmp_path: Path) -> None:
    target = _write(tmp_path / "target.py")
    link = tmp_path / "tools" / "check_zkpf_change_review.py"
    link.parent.mkdir(parents=True)
    link.symlink_to(target)
    with pytest.raises((OSError, checker.ChangeReviewError)):
        checker.explicit_change_set(
            _config(), tmp_path, ["tools/check_zkpf_change_review.py"]
        )

    link.unlink()
    _write(link)
    config = _config()
    change_set = checker.explicit_change_set(
        config, tmp_path, ["tools/check_zkpf_change_review.py"]
    )
    _, requirements = checker.classify(config, change_set)
    outside = _write(
        tmp_path / "outside.json",
        checker.canonical_json_bytes(_valid_packet(config, change_set, requirements)),
    )
    review_root = tmp_path / "reviews" / "zkpf"
    review_root.mkdir(parents=True)
    checker.required_packet_path(review_root, change_set.digest).symlink_to(outside)
    report, accepted = checker.build_report(
        config=config,
        change_set=change_set,
        review_root=review_root,
        require_review=True,
    )
    assert accepted is False
    assert report["packet_valid"] is False
