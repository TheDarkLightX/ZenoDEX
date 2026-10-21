#!/usr/bin/env python3
"""Tests for the fail-closed ZRPF soundness profile validator."""

from __future__ import annotations

import copy
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
TOOLS = REPO_ROOT / "tools"
sys.path.insert(0, str(TOOLS))

import validate_zrpf_soundness_profile as validator  # noqa: E402


EXAMPLE = REPO_ROOT / "config" / "proof_profiles" / "zrpf_risc0_3_0_5_soundness_v1.example.json"
SCHEMA = REPO_ROOT / "config" / "proof_profiles" / "zrpf_soundness_profile_v1.schema.json"


class SoundnessProfileTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.valid = json.loads(EXAMPLE.read_text(encoding="utf-8"))

    def mutated(self) -> dict:
        return copy.deepcopy(self.valid)

    def assert_invalid(self, profile: dict, fragment: str) -> None:
        with self.assertRaisesRegex(validator.ValidationError, fragment):
            validator.validate_profile(profile)

    def test_bundled_example_is_valid_and_non_authoritative(self) -> None:
        report = validator.load_and_validate(EXAMPLE)
        self.assertTrue(report["ok"])
        self.assertFalse(report["authority"])
        self.assertFalse(report["promotion_gate_passed"])
        self.assertFalse(report["counts_complete"])
        self.assertEqual(report["events"]["base"], 73)
        self.assertEqual(report["events"]["recursion"], 145)
        toy = next(item for item in report["models"] if item["model_id"] == "toy_problem_conjecture")
        self.assertAlmostEqual(toy["effective_bits"], 88.98496367319508, places=11)

    def test_schema_is_strict_json(self) -> None:
        schema = json.loads(SCHEMA.read_text(encoding="utf-8"))
        self.assertEqual(schema["$schema"], "https://json-schema.org/draft/2020-12/schema")
        self.assertFalse(schema["additionalProperties"])
        for field in validator.AUTHORITY_FIELDS:
            self.assertEqual(schema["$defs"]["authority"]["properties"][field]["const"], False)

    def test_every_authority_switch_fails_closed(self) -> None:
        for field in sorted(validator.AUTHORITY_FIELDS):
            with self.subTest(field=field):
                profile = self.mutated()
                profile["authority"][field] = True
                self.assert_invalid(profile, field)

    def test_model_and_policy_authority_fail_closed(self) -> None:
        profile = self.mutated()
        profile["models"][0]["accepted_for_authority"] = True
        self.assert_invalid(profile, "accepted_for_authority")

        profile = self.mutated()
        profile["policy"]["promotion_gate_passed"] = True
        self.assert_invalid(profile, "promotion_gate_passed")

        profile = self.mutated()
        profile["policy"]["selected_model_id"] = "toy_problem_conjecture"
        self.assert_invalid(profile, "selected_model_id")

    def test_unknown_and_missing_fields_reject(self) -> None:
        profile = self.mutated()
        profile["surprise"] = 1
        self.assert_invalid(profile, "unknown")

        profile = self.mutated()
        del profile["backend"]["commit"]
        self.assert_invalid(profile, "missing")

    def test_backend_and_circuit_drift_reject(self) -> None:
        profile = self.mutated()
        profile["backend"]["version"] = "v5.0.0-rc.1"
        self.assert_invalid(profile, "backend.version")

        profile = self.mutated()
        profile["circuit_parameters"]["global"]["fri_queries"] = 51
        self.assert_invalid(profile, "fri_queries")

        profile = self.mutated()
        profile["circuit_parameters"]["recursion"]["trace_po2"] = 19
        self.assert_invalid(profile, "trace_po2")

    def test_assumption_labels_and_exact_f32_values_reject_drift(self) -> None:
        profile = self.mutated()
        profile["models"][0]["label"] = "Unconditional proof"
        self.assert_invalid(profile, "models\\[0\\].label")

        profile = self.mutated()
        profile["models"][1]["source_function"] = "proven"
        self.assert_invalid(profile, "models\\[1\\].source_function")

        profile = self.mutated()
        profile["models"][1]["assumption_identity"] = "some list-decoding conjecture"
        self.assert_invalid(profile, "models\\[1\\].assumption_identity")

        profile = self.mutated()
        profile["models"][2]["rv32im_security_bits"]["po2_22"] += 0.001
        self.assert_invalid(profile, "po2_22")

    def test_full_tree_and_event_equations_reject_drift(self) -> None:
        profile = self.mutated()
        profile["topology"]["internal_node_count"] = 8
        self.assert_invalid(profile, "full f-ary tree equation")

        profile = self.mutated()
        profile["topology"]["total_node_count"] = 74
        self.assert_invalid(profile, "total_node_count")

        profile = self.mutated()
        profile["event_ledger"]["recursion_resolve_events"] = 71
        self.assert_invalid(profile, "one resolve")

        profile = self.mutated()
        profile["event_ledger"]["recursion_total_events"] = 144
        self.assert_invalid(profile, "recursion_total_events")

        profile = self.mutated()
        profile["event_ledger"]["counts_complete"] = True
        self.assert_invalid(profile, "counts_complete")

    def test_composition_is_recomputed(self) -> None:
        profile = self.mutated()
        profile["composition"]["per_model"][0]["epsilon_upper_bound_if_counts_exact"] *= 2
        self.assert_invalid(profile, "epsilon_upper_bound_if_counts_exact")

        profile = self.mutated()
        profile["composition"]["per_model"][2]["effective_security_bits_if_counts_exact"] += 0.1
        self.assert_invalid(profile, "effective_security_bits_if_counts_exact")

        profile = self.mutated()
        profile["composition"]["uses_rv32im_po2"] = 20
        self.assert_invalid(profile, "uses_rv32im_po2")

    def test_required_source_pin_rejects_drift(self) -> None:
        profile = self.mutated()
        profile["sources"][0]["url"] = profile["sources"][0]["url"].replace(
            validator.PINNED_COMMIT, "0" * 40
        )
        self.assert_invalid(profile, "expected exactly")

    def test_boolean_is_not_accepted_as_integer(self) -> None:
        profile = self.mutated()
        profile["topology"]["leaf_count"] = True
        self.assert_invalid(profile, "expected integer")

    def test_loader_rejects_duplicate_keys_nonfinite_and_bom(self) -> None:
        cases = {
            "duplicate": '{"schema":"a","schema":"b"}',
            "nonfinite": '{"value":NaN}',
            "bom": "\ufeff{}",
        }
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            for name, text in cases.items():
                with self.subTest(name=name):
                    path = root / f"{name}.json"
                    path.write_text(text, encoding="utf-8")
                    with self.assertRaises(validator.ValidationError):
                        validator.load_profile(path)

    def test_cli_json_result_and_failure_exit(self) -> None:
        valid = subprocess.run(
            [sys.executable, str(TOOLS / "validate_zrpf_soundness_profile.py"), str(EXAMPLE), "--json"],
            check=False,
            capture_output=True,
            text=True,
        )
        self.assertEqual(valid.returncode, 0, valid.stderr)
        self.assertTrue(json.loads(valid.stdout)["ok"])

        with tempfile.TemporaryDirectory() as temp:
            invalid_path = Path(temp) / "invalid.json"
            invalid_path.write_text("{}", encoding="utf-8")
            invalid = subprocess.run(
                [sys.executable, str(TOOLS / "validate_zrpf_soundness_profile.py"), str(invalid_path), "--json"],
                check=False,
                capture_output=True,
                text=True,
            )
        self.assertEqual(invalid.returncode, 1)
        self.assertFalse(json.loads(invalid.stdout)["ok"])


if __name__ == "__main__":
    unittest.main()
