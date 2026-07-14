from __future__ import annotations

import copy
import io
import json
import sys
import unittest
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT / "tools"))

import zrpf_level_ladder as ladder  # noqa: E402


class LadderPlannerTests(unittest.TestCase):
    def test_fanout2_depth3_is_exact_first_gate(self) -> None:
        plan = ladder.plan_ladder(2, 3)
        self.assertEqual(plan.level_node_counts, (8, 4, 2, 1))
        self.assertEqual(plan.leaf_count, 8)
        self.assertEqual(plan.internal_node_count, 7)
        self.assertEqual(plan.total_node_count, 15)
        self.assertEqual(plan.edge_count, 14)
        self.assertEqual(plan.program_image_count, 4)
        self.assertEqual(plan.capacity_class, "first_validation_gate")

    def test_fanout8_depth7_is_capacity_arithmetic_only(self) -> None:
        plan = ladder.plan_ladder(8, 7)
        self.assertEqual(
            plan.level_node_counts,
            (2_097_152, 262_144, 32_768, 4_096, 512, 64, 8, 1),
        )
        self.assertEqual(plan.leaf_count, 2_097_152)
        self.assertEqual(plan.internal_node_count, 299_593)
        self.assertEqual(plan.total_node_count, 2_396_745)
        self.assertEqual(plan.edge_count, 2_396_744)
        self.assertEqual(plan.capacity_class, "capacity_only_projection")
        emitted = plan.to_dict()
        self.assertIs(emitted["authority"], False)
        self.assertEqual(emitted["build_order"], [f"level_{level}" for level in range(8)])
        self.assertEqual(emitted["level_plan"][-1]["child_level"], 6)
        self.assertIs(emitted["level_plan"][-1]["program_image_must_be_distinct"], True)
        self.assertIn("NON_AUTHORITY_CAPACITY_ARITHMETIC_ONLY", emitted["warnings"])

    def test_bounds_reject_without_unbounded_arithmetic(self) -> None:
        cases = ((1, 3), (9, 3), (2, 0), (2, 8), (True, 3), (2, False))
        for fanout, depth in cases:
            with self.subTest(fanout=fanout, depth=depth):
                with self.assertRaises(ladder.LadderValidationError):
                    ladder.plan_ladder(fanout, depth)

    def test_cli_plan_never_reports_authority(self) -> None:
        stdout = io.StringIO()
        with redirect_stdout(stdout):
            code = ladder.main(["plan", "--fanout", "8", "--depth", "7"])
        self.assertEqual(code, 0)
        result = json.loads(stdout.getvalue())
        self.assertIs(result["authority"], False)
        self.assertEqual(result["capacity_class"], "capacity_only_projection")


class ManifestValidationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.example_path = REPO_ROOT / "config" / "proof_profiles" / "zrpf_finite_image_ladder_v1.example.json"
        cls.example = ladder.load_manifest(cls.example_path)

    def manifest(self) -> dict:
        return copy.deepcopy(self.example)

    def assert_error_code(self, manifest: dict, code: str) -> None:
        with self.assertRaises(ladder.LadderValidationError) as caught:
            ladder.validate_manifest(manifest)
        self.assertEqual(caught.exception.code, code)

    def test_example_validates_only_as_non_authority(self) -> None:
        plan = ladder.validate_manifest(self.manifest())
        receipt = ladder.validation_receipt(self.example, plan)
        self.assertEqual(receipt["status"], "VALID_NON_AUTHORITY")
        self.assertIs(receipt["authority"], False)
        self.assertEqual(receipt["evidence_status"], "specified_not_executed")

    def test_authority_true_rejects(self) -> None:
        manifest = self.manifest()
        manifest["authority"] = True
        self.assert_error_code(manifest, "value.exact")

    def test_admission_eligibility_true_rejects(self) -> None:
        manifest = self.manifest()
        manifest["assurance"]["admission_eligible"] = True
        self.assert_error_code(manifest, "value.exact")

    def test_unknown_critical_field_rejects(self) -> None:
        manifest = self.manifest()
        manifest["trust_me"] = True
        self.assert_error_code(manifest, "schema.unknown_field")

    def test_topology_count_drift_rejects(self) -> None:
        manifest = self.manifest()
        manifest["topology"]["total_node_count"] = 14
        self.assert_error_code(manifest, "value.exact")

    def test_level_skip_rejects(self) -> None:
        manifest = self.manifest()
        manifest["levels"][2]["child_binding"]["child_level"] = 0
        self.assert_error_code(manifest, "value.exact")

    def test_child_image_substitution_rejects(self) -> None:
        manifest = self.manifest()
        manifest["levels"][3]["child_binding"]["child_image_id_hex"] = "f" * 64
        self.assert_error_code(manifest, "value.exact")

    def test_parent_reusing_child_image_rejects(self) -> None:
        manifest = self.manifest()
        manifest["levels"][1]["image"]["risc0_image_id_hex"] = manifest["levels"][0]["image"][
            "risc0_image_id_hex"
        ]
        self.assert_error_code(manifest, "ladder.duplicate_image_id")

    def test_program_reuse_rejects(self) -> None:
        manifest = self.manifest()
        manifest["levels"][2]["program_id"] = manifest["levels"][1]["program_id"]
        self.assert_error_code(manifest, "ladder.duplicate_program_id")

    def test_wrong_exact_child_count_rejects(self) -> None:
        manifest = self.manifest()
        manifest["levels"][1]["child_binding"]["child_count_exact"] = 1
        self.assert_error_code(manifest, "value.exact")

    def test_nonclaim_omission_rejects(self) -> None:
        manifest = self.manifest()
        manifest["non_claims"].pop()
        self.assert_error_code(manifest, "value.exact")

    def test_boolean_cannot_smuggle_integer_topology(self) -> None:
        manifest = self.manifest()
        manifest["topology"]["fanout"] = True
        self.assert_error_code(manifest, "type.integer")

    def test_duplicate_json_key_rejects(self) -> None:
        text = '{"authority":false,"authority":true}'
        with self.assertRaises(ladder.LadderValidationError) as caught:
            ladder.loads_json_strict(text)
        self.assertEqual(caught.exception.code, "json.duplicate_key")

    def test_non_finite_json_number_rejects(self) -> None:
        with self.assertRaises(ladder.LadderValidationError) as caught:
            ladder.loads_json_strict('{"fanout":NaN}')
        self.assertEqual(caught.exception.code, "json.non_finite_number")

    def test_cli_validation_receipt_is_explicitly_non_authority(self) -> None:
        stdout = io.StringIO()
        stderr = io.StringIO()
        with redirect_stdout(stdout), redirect_stderr(stderr):
            code = ladder.main(["validate", str(self.example_path)])
        self.assertEqual(code, 0, stderr.getvalue())
        receipt = json.loads(stdout.getvalue())
        self.assertEqual(receipt["status"], "VALID_NON_AUTHORITY")
        self.assertIs(receipt["authority"], False)


class EssoArtifactTests(unittest.TestCase):
    def test_candidate_ir_shape_and_authority_nonclaim(self) -> None:
        model_path = REPO_ROOT / "docs" / "research" / "models" / "ZRPF_FINITE_LADDER_DEPTH3_ESSO_V1.json"
        model = json.loads(model_path.read_text(encoding="utf-8"))
        self.assertEqual(model["ir_version"], "esso-ir/v1")
        self.assertEqual(
            model["meta"]["esso_revision"],
            "db8a3f8a782a508ada5005a2cf177f25c58f451d",
        )
        self.assertIs(model["meta"]["authority"], False)
        self.assertEqual(model["meta"]["bounds"]["fanout"], 2)
        self.assertEqual(model["meta"]["bounds"]["depth"], 3)
        state_ids = {item["id"] for item in model["state_vars"]}
        self.assertEqual(
            state_ids,
            {
                "authority",
                "built_level",
                "constructed_nodes",
                "covered_leaves",
                "gate_complete",
                "last_image",
            },
        )
        action_ids = [item["id"] for item in model["actions"]]
        self.assertEqual(
            action_ids,
            ["build_level_1", "build_level_2", "build_level_3", "finalize_non_authority_gate"],
        )

    def test_campaign_is_unexecuted_and_fail_closed(self) -> None:
        campaign_path = REPO_ROOT / "docs" / "research" / "models" / "ZRPF_FINITE_LADDER_DEPTH3_ESSO_CAMPAIGN_V1.json"
        campaign = json.loads(campaign_path.read_text(encoding="utf-8"))
        self.assertEqual(campaign["execution_status"], "specified_not_executed")
        self.assertEqual(campaign["unknown_policy"], "fail")
        self.assertIs(campaign["authority"], False)
        self.assertIn("esso_executable_sha256", campaign["result_receipt_required_fields"])
        self.assertIn("counterexample_artifacts", campaign["result_receipt_required_fields"])


if __name__ == "__main__":
    unittest.main()
