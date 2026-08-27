from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SCANNER = ROOT / "tools" / "scan_lean_proof_placeholders_v1.py"

CLEAN_PROOF = """/-!
A doc comment that talks about how we admit nothing, never write sorry,
and take no axiom on trust. It also asks a question here.
-/
namespace Demo

-- ordinary line comment mentioning sorry and admit and axiom
def two : Nat := 2

theorem two_eq : two = 2 := rfl

def label : String := "sorry admit axiom unsafe"

end Demo
"""


def _run(*args: str) -> tuple[int, dict]:
    result = subprocess.run(
        [sys.executable, str(SCANNER), *args, "--json"],
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=120,
        check=False,
    )
    return result.returncode, json.loads(result.stdout)


def _write(tmp_path: Path, name: str, body: str) -> Path:
    target = tmp_path / name
    target.write_text(body, encoding="utf-8")
    return target


def test_scanner_exists_in_repository() -> None:
    assert SCANNER.is_file(), "the placeholder gate must be repository-owned"


def test_clean_proof_passes_and_reports_axiom_checking(tmp_path: Path) -> None:
    target = _write(tmp_path, "Clean.lean", CLEAN_PROOF)
    code, payload = _run(str(target))
    assert code == 0
    assert payload["blocked"] is False
    assert payload["match_count"] == 0
    assert payload["axiom_check"] is True
    assert payload["scanned_files"] == [str(target)]


def test_prose_and_strings_do_not_block(tmp_path: Path) -> None:
    """The regression that motivated replacing the machine-local scanner."""
    target = _write(tmp_path, "Prose.lean", CLEAN_PROOF)
    code, payload = _run(str(target))
    assert code == 0, payload
    assert payload["matches"] == []


def test_question_mark_in_prose_does_not_block(tmp_path: Path) -> None:
    body = "/-- Does this block? It must not. -/\ndef ok : Nat := 1\n"
    target = _write(tmp_path, "Question.lean", body)
    code, payload = _run(str(target))
    assert code == 0, payload


def test_sorry_in_tactic_position_blocks(tmp_path: Path) -> None:
    body = "theorem bad : 1 = 1 := by\n  sorry\n"
    target = _write(tmp_path, "Sorry.lean", body)
    code, payload = _run(str(target))
    assert code == 1
    assert payload["blocked"] is True
    rules = {m["rule"] for m in payload["matches"]}
    assert "lean_sorry" in rules
    assert payload["matches"][0]["line"] == 2


def test_admit_in_tactic_position_blocks(tmp_path: Path) -> None:
    body = "theorem bad : 1 = 1 := by\n  admit\n"
    target = _write(tmp_path, "Admit.lean", body)
    code, payload = _run(str(target))
    assert code == 1
    assert "lean_admit" in {m["rule"] for m in payload["matches"]}


def test_admitted_identifier_does_not_block(tmp_path: Path) -> None:
    body = "def admitted : Nat := 1\ndef sorryish : Nat := 2\n"
    target = _write(tmp_path, "Identifiers.lean", body)
    code, payload = _run(str(target))
    assert code == 0, payload


def test_axiom_declaration_blocks_by_default(tmp_path: Path) -> None:
    body = "axiom trustMe : 1 = 2\n"
    target = _write(tmp_path, "Axiom.lean", body)
    code, payload = _run(str(target))
    assert code == 1
    assert "lean_axiom_declaration" in {m["rule"] for m in payload["matches"]}


def test_constant_declaration_blocks_by_default(tmp_path: Path) -> None:
    body = "constant trustMe : 1 = 2\n"
    target = _write(tmp_path, "Constant.lean", body)
    code, payload = _run(str(target))
    assert code == 1
    assert "lean_constant_declaration" in {m["rule"] for m in payload["matches"]}


def test_attributed_and_modified_axiom_declaration_blocks(tmp_path: Path) -> None:
    body = "@[simp] private axiom trustMe : 1 = 2\n"
    target = _write(tmp_path, "AxiomModified.lean", body)
    code, payload = _run(str(target))
    assert code == 1
    assert "lean_axiom_declaration" in {m["rule"] for m in payload["matches"]}


def test_allow_axioms_flag_relaxes_only_the_axiom_rule(tmp_path: Path) -> None:
    body = "axiom trustMe : 1 = 2\nconstant trustMeToo : 2 = 3\n"
    target = _write(tmp_path, "AxiomAllowed.lean", body)
    code, payload = _run(str(target), "--allow-axioms")
    assert code == 0
    assert payload["axiom_check"] is False

    body_with_sorry = "axiom trustMe : 1 = 2\ntheorem bad : 1 = 1 := by\n  sorry\n"
    target2 = _write(tmp_path, "AxiomAndSorry.lean", body_with_sorry)
    code2, payload2 = _run(str(target2), "--allow-axioms")
    assert code2 == 1
    assert {m["rule"] for m in payload2["matches"]} == {"lean_sorry"}


def test_unsafe_declaration_blocks(tmp_path: Path) -> None:
    body = "unsafe def loop : Nat := loop\n"
    target = _write(tmp_path, "Unsafe.lean", body)
    code, payload = _run(str(target))
    assert code == 1
    assert "lean_unsafe_declaration" in {m["rule"] for m in payload["matches"]}


def test_native_decide_blocks(tmp_path: Path) -> None:
    body = "theorem bad : 1 = 1 := by\n  native_decide\n"
    target = _write(tmp_path, "NativeDecide.lean", body)
    code, payload = _run(str(target))
    assert code == 1
    assert "lean_native_decide" in {m["rule"] for m in payload["matches"]}


def test_nested_block_comment_is_stripped(tmp_path: Path) -> None:
    body = "/- outer /- inner sorry -/ still comment sorry -/\ndef ok : Nat := 1\n"
    target = _write(tmp_path, "Nested.lean", body)
    code, payload = _run(str(target))
    assert code == 0, payload


def test_unterminated_block_comment_fails_closed(tmp_path: Path) -> None:
    body = "/- open comment\ntheorem bad : 1 = 1 := by sorry\n"
    target = _write(tmp_path, "Unterminated.lean", body)
    code, payload = _run(str(target))
    assert code == 2
    assert payload["blocked"] is True
    assert "unterminated block comment" in payload["error"]


def test_unterminated_string_fails_closed(tmp_path: Path) -> None:
    body = 'def hidden : String := "sorry\n'
    target = _write(tmp_path, "UnterminatedString.lean", body)
    code, payload = _run(str(target))
    assert code == 2
    assert payload["blocked"] is True
    assert "unterminated string literal" in payload["error"]


def test_missing_path_fails_closed(tmp_path: Path) -> None:
    code, payload = _run(str(tmp_path / "Absent.lean"))
    assert code == 2
    assert payload["blocked"] is True
    assert "does not exist" in payload["error"]


def test_non_proof_suffix_fails_closed(tmp_path: Path) -> None:
    target = _write(tmp_path, "notes.txt", "sorry\n")
    code, payload = _run(str(target))
    assert code == 2
    assert payload["blocked"] is True
    assert "not a .lean proof file" in payload["error"]


def test_empty_and_whitespace_only_proofs_fail_closed(tmp_path: Path) -> None:
    for name, body in (("Empty.lean", ""), ("Whitespace.lean", " \n\t")):
        target = _write(tmp_path, name, body)
        code, payload = _run(str(target))
        assert code == 2
        assert payload["blocked"] is True
        assert payload["matches"] == []
        assert "empty or whitespace-only proof file" in payload["error"]


def test_directory_without_proof_files_fails_closed(tmp_path: Path) -> None:
    empty = tmp_path / "empty"
    empty.mkdir()
    (empty / "readme.md").write_text("nothing here\n", encoding="utf-8")
    code, payload = _run(str(empty))
    assert code == 2
    assert payload["blocked"] is True
    assert "no .lean proof files" in payload["error"]


def test_directory_scan_recurses_and_reports_each_file(tmp_path: Path) -> None:
    tree = tmp_path / "tree"
    (tree / "nested").mkdir(parents=True)
    (tree / "A.lean").write_text("def a : Nat := 1\n", encoding="utf-8")
    (tree / "nested" / "B.lean").write_text(
        "theorem b : 1 = 1 := by\n  sorry\n", encoding="utf-8"
    )
    code, payload = _run(str(tree))
    assert code == 1
    assert len(payload["scanned_files"]) == 2
    assert payload["match_count"] == 1
    assert payload["matches"][0]["path"].endswith("B.lean")


def test_custom_suffix_is_honoured(tmp_path: Path) -> None:
    target = _write(tmp_path, "Proof.lean4", "theorem bad : 1 = 1 := by sorry\n")
    code, _ = _run(str(target), "--suffix", ".lean4")
    assert code == 1
    code2, payload2 = _run(str(target))
    assert code2 == 2
    assert "not a .lean proof file" in payload2["error"]


def test_duplicate_paths_are_scanned_once(tmp_path: Path) -> None:
    target = _write(tmp_path, "Dup.lean", "def ok : Nat := 1\n")
    code, payload = _run(str(target), str(target))
    assert code == 0
    assert payload["scanned_files"] == [str(target)]


def test_repository_proof_targets_are_clean() -> None:
    proof = ROOT / "lean-mathlib" / "Proofs" / "GlobalSettlementCoreV1.lean"
    challenge = ROOT / "lean-mathlib" / "Proofs" / "GlobalSettlementCoreV1Challenge.lean"
    code, payload = _run(str(proof), str(challenge))
    assert code == 0, payload
    assert payload["axiom_check"] is True
    assert len(payload["scanned_files"]) == 2
