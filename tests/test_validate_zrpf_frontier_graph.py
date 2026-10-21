from __future__ import annotations

import contextlib
import copy
import hashlib
import io
import json
import sys
import tempfile
import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
TOOLS = REPO_ROOT / "tools"
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

import validate_zrpf_frontier_graph as validator  # noqa: E402


def _assumption(dependency_id: str = "dep_example") -> dict[str, str]:
    return {
        "dependency_id": dependency_id,
        "assumed_statement": "The dependency is established.",
        "required_state": "PROVEN",
        "version_requirement": "example=1",
        "failure_effect": "BLOCK_PROMOTION",
        "rationale": "The candidate is unsound without it.",
    }


def _graph(state: str = "PROVEN") -> dict[str, object]:
    drifted = state == "VERSION_DRIFTED"
    blockers = [] if state == "PROVEN" else ["dep_example"]
    return {
        "schema": validator.SCHEMA,
        "as_of": "2026-07-14",
        "repository": {
            "full_name": "owner/repo",
            "default_branch": "main",
            "default_branch_sha": "a" * 40,
            "integration_pr": 1,
            "integration_head_sha": "b" * 40,
        },
        "source_graph": {
            "path": "source.json",
            "sha256": "0" * 64,
            "schema": validator.SOURCE_SCHEMA,
            "run_id": "run-1",
        },
        "dependency_states": sorted(validator.DEPENDENCY_STATES),
        "dependencies": [
            {
                "id": "dep_example",
                "statement": "A versioned dependency.",
                "state": state,
                "version": {
                    "component": "example",
                    "expected": "2" if drifted else "1",
                    "observed": "1",
                    "source_revision": "fixture:1",
                },
                "evidence_refs": ["fixture:evidence"],
            }
        ],
        "candidates": [
            {
                "id": "h_example",
                "origin": "repository_recon",
                "content": "Test a candidate.",
                "selected": True,
                "promotion_decision": "BLOCKED" if blockers else "ELIGIBLE",
                "blockers": blockers,
                "assumption_dependencies": [_assumption()],
            }
        ],
        "non_claims": ["Fixture success is not production evidence."],
    }


def _source_graph() -> dict[str, object]:
    return {
        "schema": validator.SOURCE_SCHEMA,
        "graph": {"run_id": "run-1", "atoms": []},
    }


class GraphValidationTests(unittest.TestCase):
    def test_minimal_proven_graph_is_eligible(self) -> None:
        graph = _graph()
        self.assertEqual(validator.validate_graph(graph), [])
        self.assertEqual(validator.selected_blockers(graph), {})

    def test_selected_candidate_requires_assumption_dependencies(self) -> None:
        graph = _graph()
        graph["candidates"][0]["assumption_dependencies"] = []  # type: ignore[index]
        errors = validator.validate_graph(graph)
        self.assertTrue(any("assumption_dependencies" in error for error in errors))

    def test_unproven_dependency_blocks_without_invalidating_graph(self) -> None:
        graph = _graph("UNPROVEN")
        self.assertEqual(validator.validate_graph(graph), [])
        self.assertEqual(
            validator.selected_blockers(graph), {"h_example": ["dep_example"]}
        )

    def test_disproven_dependency_blocks(self) -> None:
        graph = _graph("DISPROVEN")
        self.assertEqual(validator.validate_graph(graph), [])
        self.assertEqual(
            validator.selected_blockers(graph), {"h_example": ["dep_example"]}
        )

    def test_version_drifted_dependency_blocks(self) -> None:
        graph = _graph("VERSION_DRIFTED")
        self.assertEqual(validator.validate_graph(graph), [])
        self.assertEqual(
            validator.selected_blockers(graph), {"h_example": ["dep_example"]}
        )

    def test_candidate_cannot_claim_eligible_with_unproven_dependency(self) -> None:
        graph = _graph("UNPROVEN")
        candidate = graph["candidates"][0]  # type: ignore[index]
        candidate["promotion_decision"] = "ELIGIBLE"
        candidate["blockers"] = []
        errors = validator.validate_graph(graph)
        self.assertTrue(any("computed blockers" in error for error in errors))
        self.assertTrue(any("must be BLOCKED" in error for error in errors))

    def test_required_state_cannot_be_weakened(self) -> None:
        graph = _graph("UNPROVEN")
        assumption = graph["candidates"][0]["assumption_dependencies"][0]  # type: ignore[index]
        assumption["required_state"] = "UNPROVEN"
        errors = validator.validate_graph(graph)
        self.assertTrue(any("required_state must be PROVEN" in error for error in errors))

    def test_proven_dependency_cannot_hide_version_mismatch(self) -> None:
        graph = _graph("PROVEN")
        version = graph["dependencies"][0]["version"]  # type: ignore[index]
        version["expected"] = "2"
        errors = validator.validate_graph(graph)
        self.assertTrue(any("claims PROVEN" in error for error in errors))

    def test_version_drift_state_requires_a_mismatch(self) -> None:
        graph = _graph("VERSION_DRIFTED")
        version = graph["dependencies"][0]["version"]  # type: ignore[index]
        version["expected"] = version["observed"]
        errors = validator.validate_graph(graph)
        self.assertTrue(any("claims VERSION_DRIFTED" in error for error in errors))

    def test_unknown_dependency_is_rejected(self) -> None:
        graph = _graph()
        graph["candidates"][0]["assumption_dependencies"][0][  # type: ignore[index]
            "dependency_id"
        ] = "dep_missing"
        errors = validator.validate_graph(graph)
        self.assertTrue(any("unknown dependency" in error for error in errors))

    def test_duplicate_dependency_id_is_rejected(self) -> None:
        graph = _graph()
        graph["dependencies"].append(copy.deepcopy(graph["dependencies"][0]))  # type: ignore[union-attr,index]
        errors = validator.validate_graph(graph)
        self.assertIn("duplicate dependency id: dep_example", errors)


class SourceGraphTests(unittest.TestCase):
    def test_source_digest_and_research_kernel_candidate_are_checked(self) -> None:
        graph = _graph()
        candidate = graph["candidates"][0]  # type: ignore[index]
        candidate["origin"] = "research_kernel"
        source = _source_graph()
        source["graph"]["atoms"] = [  # type: ignore[index]
            {
                "id": "h_example",
                "type": "HYPOTHESIS",
                "content": candidate["content"],
                "metadata": {"selected_for_pr": True},
            }
        ]
        with tempfile.TemporaryDirectory() as temp_dir:
            path = Path(temp_dir) / "source.json"
            encoded = json.dumps(source, sort_keys=True).encode("utf-8")
            path.write_bytes(encoded)
            graph["source_graph"]["sha256"] = hashlib.sha256(encoded).hexdigest()  # type: ignore[index]
            self.assertEqual(validator.validate_source_graph(graph, path), [])

            candidate["content"] = "Drifted content."
            errors = validator.validate_source_graph(graph, path)
            self.assertTrue(any("content differs" in error for error in errors))

    def test_source_digest_mismatch_is_rejected(self) -> None:
        graph = _graph()
        with tempfile.TemporaryDirectory() as temp_dir:
            path = Path(temp_dir) / "source.json"
            path.write_text(json.dumps(_source_graph()), encoding="utf-8")
            errors = validator.validate_source_graph(graph, path)
            self.assertTrue(any("digest mismatch" in error for error in errors))


class CommandLineTests(unittest.TestCase):
    def _run_main(self, graph: dict[str, object], admission: bool) -> tuple[int, dict[str, object]]:
        source = _source_graph()
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            source_path = root / "source.json"
            source_bytes = json.dumps(source, sort_keys=True).encode("utf-8")
            source_path.write_bytes(source_bytes)
            graph["source_graph"]["sha256"] = hashlib.sha256(source_bytes).hexdigest()  # type: ignore[index]
            graph_path = root / "decision.json"
            graph_path.write_text(json.dumps(graph), encoding="utf-8")
            argv = [str(graph_path), "--source-graph", str(source_path), "--json"]
            if admission:
                argv.append("--admission")
            output = io.StringIO()
            with contextlib.redirect_stdout(output):
                code = validator.main(argv)
            return code, json.loads(output.getvalue())

    def test_structural_mode_accepts_honestly_blocked_graph(self) -> None:
        code, result = self._run_main(_graph("UNPROVEN"), admission=False)
        self.assertEqual(code, 0)
        self.assertTrue(result["ok"])
        self.assertEqual(result["selected_blockers"], {"h_example": ["dep_example"]})

    def test_admission_mode_returns_two_for_blocked_selection(self) -> None:
        code, result = self._run_main(_graph("DISPROVEN"), admission=True)
        self.assertEqual(code, 2)
        self.assertFalse(result["ok"])
        self.assertEqual(result["errors"], [])
        self.assertEqual(result["selected_blockers"], {"h_example": ["dep_example"]})

    def test_admission_mode_accepts_proven_selection(self) -> None:
        code, result = self._run_main(_graph("PROVEN"), admission=True)
        self.assertEqual(code, 0)
        self.assertTrue(result["ok"])
        self.assertEqual(result["selected_blockers"], {})


if __name__ == "__main__":
    unittest.main()

