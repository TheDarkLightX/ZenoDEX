from __future__ import annotations

import copy
import importlib.util
import json
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[1]
CHECKER_PATH = REPO / "tools/check_risc0_recursive_active_reproof_v3.py"
SPEC = importlib.util.spec_from_file_location("active_reproof_v3_checker", CHECKER_PATH)
assert SPEC is not None and SPEC.loader is not None
checker = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(checker)


def reference() -> dict[str, object]:
    return json.loads(checker.REFERENCE.read_bytes())


def test_active_reproof_reference_accepts() -> None:
    checker.validate(reference())


@pytest.mark.parametrize(
    "mutation",
    [
        lambda value: value["claims"].__setitem__("production_authority", True),
        lambda value: value["claims"].__setitem__("privacy_or_zero_knowledge", 0),
        lambda value: value["programs"][0].__setitem__("image_id", "00" * 32),
        lambda value: value["host_binaries"][2].__setitem__("sha256", "11" * 32),
        lambda value: value.__setitem__("unknown", False),
    ],
)
def test_active_reproof_reference_rejects_authority_and_identity_mutations(mutation) -> None:
    candidate = copy.deepcopy(reference())
    mutation(candidate)
    with pytest.raises(checker.CheckError):
        checker.validate(candidate)


def test_active_reproof_reference_rejects_coherent_evidence_rebinding() -> None:
    candidate = copy.deepcopy(reference())
    candidate["evidence"]["files"][0]["sha256"] = "22" * 32
    candidate["evidence"]["inventory_root"] = "33" * 32
    with pytest.raises(checker.CheckError, match="evidence reference mismatch"):
        checker.validate(candidate)


def test_strict_loader_rejects_duplicate_keys(tmp_path: Path) -> None:
    candidate = tmp_path / "duplicate.json"
    candidate.write_text('{"schema":1,"schema":2}', encoding="utf-8")
    with pytest.raises(checker.CheckError, match="duplicate JSON key"):
        checker.load_json(candidate)


def test_strict_loader_rejects_symlink(tmp_path: Path) -> None:
    target = tmp_path / "target.json"
    target.write_text("{}", encoding="utf-8")
    candidate = tmp_path / "candidate.json"
    candidate.symlink_to(target)
    with pytest.raises(checker.CheckError, match="bounded regular file"):
        checker.load_json(candidate)


def test_inventory_rejects_symlink_and_target_directory(tmp_path: Path) -> None:
    source = tmp_path / "source"
    source.mkdir()
    ordinary = source / "ordinary.json"
    ordinary.write_text("{}", encoding="utf-8")
    alias = source / "alias.json"
    alias.symlink_to(ordinary)
    with pytest.raises(checker.CheckError, match="inventory symlink rejected"):
        checker.inventory(source, repo_root=tmp_path)

    alias.unlink()
    (source / "target").mkdir()
    with pytest.raises(checker.CheckError, match="in-scope target directory rejected"):
        checker.inventory(source, repo_root=tmp_path)


def test_active_reproof_requires_the_governed_git_base(tmp_path: Path) -> None:
    with pytest.raises(checker.CheckError):
        checker._check_git_base(tmp_path)


def test_exact_typed_comparison_rejects_integer_boolean_aliases() -> None:
    for value, expected in ((1, True), (0, False), (True, 1), (False, 0)):
        with pytest.raises(checker.CheckError):
            checker._require_exact_typed(value, expected, "type mismatch")


def test_promotion_source_inventory_is_bound() -> None:
    candidate = copy.deepcopy(reference())
    candidate["promotion_source_inventory"]["files"][0]["sha256"] = "44" * 32
    with pytest.raises(checker.CheckError, match="promotion source inventory mismatch"):
        checker.validate(candidate)


def test_active_reproof_binds_v2_inputs_to_exact_v1_receipts(monkeypatch) -> None:
    original = checker.load_json

    def altered(path: Path):
        value = original(path)
        if path.name == "v2-reversed.dry-run.json":
            value["input_leaf_receipt_sha256s"] = ["55" * 32, "66" * 32]
        return value

    monkeypatch.setattr(checker, "load_json", altered)
    with pytest.raises(checker.CheckError, match="bind retained V1 leaf receipts"):
        checker.validate(reference())


def test_active_reproof_recomputes_v1_child_claims(monkeypatch) -> None:
    original = checker.load_json

    def altered(path: Path):
        value = original(path)
        if path.name == "v1-root.verify.json":
            value["verified_recursive_facts"]["child_verification_claim_hashes"][0] = "0x" + "77" * 32
        return value

    monkeypatch.setattr(checker, "load_json", altered)
    with pytest.raises(checker.CheckError, match="V1 positive transcript mismatch"):
        checker.validate(reference())


def test_active_reproof_reports_require_exact_boolean_types(monkeypatch) -> None:
    original = checker.load_json

    def altered(path: Path):
        value = original(path)
        if path.name == "v2-pair.verify.json":
            value["ok"] = 1
        return value

    monkeypatch.setattr(checker, "load_json", altered)
    with pytest.raises(checker.CheckError, match="V2 pair transcript mismatch"):
        checker.validate(reference())


def test_active_reproof_binds_supplied_reverse_order_and_full_report(monkeypatch) -> None:
    original = checker.load_json

    def altered(path: Path):
        value = original(path)
        if path.name == "v2-reversed.dry-run.json":
            value["supplied_leaf_receipt_sha256s"] = value["input_leaf_receipt_sha256s"]
            value["dry_run"] = 1
        return value

    monkeypatch.setattr(checker, "load_json", altered)
    with pytest.raises(checker.CheckError, match="reverse dry-run mismatch"):
        checker.validate(reference())

def test_exact_seal_control_rejects_an_additional_outer_mutation() -> None:
    source = checker.load_json(checker.EVIDENCE / "receipts/v2-root.proof.json")
    mutated = checker.load_json(
        checker.EVIDENCE / "controls/v2-root.seal-word-1-xor-lsb.proof.json"
    )
    checker._check_exact_seal_mutation(source, mutated)

    rebound = copy.deepcopy(mutated)
    rebound["receipt_kind"] = "composite"
    with pytest.raises(checker.CheckError, match="seal mutation changed outer fields"):
        checker._check_exact_seal_mutation(source, rebound)
