from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO / "tools"))

from zenodex_oracle_query_policy import (  # noqa: E402
    MAX_PREFLIGHT_BYTES,
    MAX_PREFLIGHT_REPORTERS,
    PREFLIGHT_NOT_CLAIMED,
    PREFLIGHT_PREMISE,
    PREFLIGHT_RESULT_SCHEMA,
    content_hash,
    preflight_policy_revision,
    sample_hash,
    sample_policy_trace,
    sample_preflight_context,
    verify_policy_trace,
)


def _reporters(count: int) -> list[str]:
    return sorted(sample_hash(f"preflight-reporter-{pos}") for pos in range(count))


def _trace_with_reporter_quorum(quorum: int) -> dict:
    trace = sample_policy_trace()
    v1 = trace["events"][0]["policy"]
    v2 = trace["events"][2]["policy"]
    v1["min_distinct_reporters"] = quorum
    v1["policy_id"] = content_hash(v1, omit_key="policy_id")
    trace["events"][1]["policy_id"] = v1["policy_id"]
    v2["min_distinct_reporters"] = quorum
    v2["supersedes_policy_id"] = v1["policy_id"]
    v2["policy_id"] = content_hash(v2, omit_key="policy_id")
    return trace


def _run_cli(*args: str) -> tuple[int, dict]:
    proc = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_query_policy.py", *args],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.stderr == ""
    return proc.returncode, json.loads(proc.stdout)


def _write(tmp_path: Path, name: str, text: str) -> str:
    path = tmp_path / name
    path.write_text(text, encoding="utf-8")
    return str(path)


# --- BDD controls -----------------------------------------------------------


def test_given_accepted_revision_and_matching_context_then_preflight_accepts() -> None:
    result = preflight_policy_revision(sample_policy_trace(), sample_preflight_context())
    assert result.status == "accepted"
    assert result.errors == []
    assert result.min_distinct_reporters == 3
    assert result.eligible_reporter_count == 3


def test_given_success_then_output_states_research_premise_and_nonclaims() -> None:
    obj = preflight_policy_revision(sample_policy_trace(), sample_preflight_context()).to_json_obj()
    assert obj["schema"] == PREFLIGHT_RESULT_SCHEMA
    assert obj["ok"] is True
    assert obj["premise"] == PREFLIGHT_PREMISE == "research_preflight_necessary_condition_only"
    for claim in (
        "does_not_claim_authenticated_reporter_registry",
        "does_not_claim_source_quorum",
        "does_not_claim_reporter_liveness",
        "does_not_claim_reporter_authority",
        "does_not_claim_sufficient_condition",
    ):
        assert claim in obj["not_claimed"]
    assert obj["not_claimed"] == PREFLIGHT_NOT_CLAIMED


def test_given_too_few_eligible_reporters_then_preflight_rejects() -> None:
    context = sample_preflight_context()
    context["eligible_reporter_ids"] = _reporters(2)
    result = preflight_policy_revision(sample_policy_trace(), context)
    assert result.status == "rejected"
    assert "eligible_reporters_below_reporter_quorum:2<3" in result.errors


# --- Trace and lineage ------------------------------------------------------


def test_rejected_trace_never_preflights() -> None:
    trace = sample_policy_trace()
    trace["events"][2]["policy"]["max_deviation_bps"] = 250
    context = sample_preflight_context(trace)
    result = preflight_policy_revision(trace, context)
    assert result.status == "rejected"
    assert "trace_not_accepted" in result.errors
    assert "trace:policy_content_hash_mismatch:" + trace["events"][2]["policy"]["policy_id"] in result.errors


def test_single_policy_trace_is_not_a_revision() -> None:
    trace = sample_policy_trace()
    del trace["events"][2]
    assert verify_policy_trace(trace).status == "accepted"
    context = sample_preflight_context()
    result = preflight_policy_revision(trace, context)
    assert result.status == "rejected"
    assert "preflight_requires_policy_revision" in result.errors


def test_swapped_current_and_candidate_ids_rejected() -> None:
    context = sample_preflight_context()
    context["current_policy_id"], context["candidate_policy_id"] = (
        context["candidate_policy_id"],
        context["current_policy_id"],
    )
    result = preflight_policy_revision(sample_policy_trace(), context)
    assert result.status == "rejected"
    assert "context_current_policy_id_mismatch" in result.errors
    assert "context_candidate_policy_id_mismatch" in result.errors


def test_wrong_query_id_rejected() -> None:
    context = sample_preflight_context()
    context["query_id"] = sample_hash("other-query")
    result = preflight_policy_revision(sample_policy_trace(), context)
    assert result.status == "rejected"
    assert result.errors == ["context_query_id_mismatch"]


# --- Malformed context --------------------------------------------------------


@pytest.mark.parametrize("context", [None, [], "x", 1, True])
def test_non_object_context_rejected(context: object) -> None:
    result = preflight_policy_revision(sample_policy_trace(), context)
    assert result.status == "rejected"
    assert result.errors == ["context_must_be_object"]


def test_non_object_trace_rejected() -> None:
    result = preflight_policy_revision([], sample_preflight_context())
    assert result.status == "rejected"
    assert result.errors == ["trace_must_be_object"]


def test_empty_context_rejected_with_every_field_missing() -> None:
    result = preflight_policy_revision(sample_policy_trace(), {})
    assert result.status == "rejected"
    assert "preflight_context_schema_mismatch" in result.errors
    assert "query_id_must_be_canonical_sha256" in result.errors
    assert "current_policy_id_must_be_canonical_sha256" in result.errors
    assert "candidate_policy_id_must_be_canonical_sha256" in result.errors
    assert "eligible_reporter_ids_must_be_list" in result.errors


def test_unknown_context_field_rejected() -> None:
    context = sample_preflight_context()
    context["source_quorum_ok"] = True
    result = preflight_policy_revision(sample_policy_trace(), context)
    assert result.status == "rejected"
    assert result.errors == ["unknown_preflight_context_field:source_quorum_ok"]


def test_wrong_schema_rejected() -> None:
    context = sample_preflight_context()
    context["schema"] = "zenodex.oracle.query_policy_trace.v1"
    result = preflight_policy_revision(sample_policy_trace(), context)
    assert result.status == "rejected"
    assert result.errors == ["preflight_context_schema_mismatch"]


@pytest.mark.parametrize("key", ["query_id", "current_policy_id", "candidate_policy_id"])
def test_trailing_newline_id_rejected(key: str) -> None:
    context = sample_preflight_context()
    context[key] = context[key] + "\n"
    result = preflight_policy_revision(sample_policy_trace(), context)
    assert result.status == "rejected"
    assert result.errors == [f"{key}_must_be_canonical_sha256"]


@pytest.mark.parametrize("key", ["query_id", "current_policy_id", "candidate_policy_id"])
def test_bool_id_rejected(key: str) -> None:
    context = sample_preflight_context()
    context[key] = True
    result = preflight_policy_revision(sample_policy_trace(), context)
    assert result.status == "rejected"
    assert result.errors == [f"{key}_must_be_canonical_sha256"]


@pytest.mark.parametrize("bad", [True, False, 3, "sha256:", {}, None])
def test_reporter_ids_not_list_rejected(bad: object) -> None:
    context = sample_preflight_context()
    context["eligible_reporter_ids"] = bad
    result = preflight_policy_revision(sample_policy_trace(), context)
    assert result.status == "rejected"
    assert result.errors == ["eligible_reporter_ids_must_be_list"]
    assert result.eligible_reporter_count is None


def test_reporter_id_trailing_newline_rejected() -> None:
    context = sample_preflight_context()
    context["eligible_reporter_ids"][1] = context["eligible_reporter_ids"][1] + "\n"
    result = preflight_policy_revision(sample_policy_trace(), context)
    assert result.status == "rejected"
    assert result.errors == ["eligible_reporter_id_1_must_be_canonical_sha256"]


def test_reporter_id_uppercase_hex_rejected() -> None:
    context = sample_preflight_context()
    lowered = context["eligible_reporter_ids"][0]
    context["eligible_reporter_ids"][0] = "sha256:" + lowered[len("sha256:"):].upper()
    result = preflight_policy_revision(sample_policy_trace(), context)
    assert result.status == "rejected"
    assert result.errors == ["eligible_reporter_id_0_must_be_canonical_sha256"]


def test_bool_reporter_id_rejected() -> None:
    context = sample_preflight_context()
    context["eligible_reporter_ids"] = [True] + _reporters(3)
    result = preflight_policy_revision(sample_policy_trace(), context)
    assert result.status == "rejected"
    assert result.errors == ["eligible_reporter_id_0_must_be_canonical_sha256"]


def test_duplicate_reporter_ids_rejected_and_not_counted() -> None:
    context = sample_preflight_context()
    ids = _reporters(3)
    context["eligible_reporter_ids"] = [ids[0], ids[0], ids[1], ids[2]]
    result = preflight_policy_revision(sample_policy_trace(), context)
    assert result.status == "rejected"
    assert result.errors == ["eligible_reporter_ids_must_be_sorted_unique:1"]
    assert result.eligible_reporter_count is None


def test_unsorted_reporter_ids_rejected() -> None:
    context = sample_preflight_context()
    context["eligible_reporter_ids"] = list(reversed(_reporters(3)))
    result = preflight_policy_revision(sample_policy_trace(), context)
    assert result.status == "rejected"
    assert "eligible_reporter_ids_must_be_sorted_unique:1" in result.errors


# --- Boundaries --------------------------------------------------------------


def test_boundary_quorum_equals_population_accepts() -> None:
    context = sample_preflight_context()
    context["eligible_reporter_ids"] = _reporters(3)
    assert preflight_policy_revision(sample_policy_trace(), context).status == "accepted"


def test_boundary_zero_reporters_rejected_for_minimum_quorum() -> None:
    trace = _trace_with_reporter_quorum(1)
    context = sample_preflight_context(trace)
    context["eligible_reporter_ids"] = []
    result = preflight_policy_revision(trace, context)
    assert result.status == "rejected"
    assert "eligible_reporters_below_reporter_quorum:0<1" in result.errors


def test_boundary_population_at_bound_accepts_max_quorum() -> None:
    trace = _trace_with_reporter_quorum(64)
    context = sample_preflight_context(trace)
    context["eligible_reporter_ids"] = _reporters(MAX_PREFLIGHT_REPORTERS)
    result = preflight_policy_revision(trace, context)
    assert result.status == "accepted"
    assert result.eligible_reporter_count == 64


def test_boundary_population_over_bound_is_inconclusive_not_rejected() -> None:
    context = sample_preflight_context()
    context["eligible_reporter_ids"] = _reporters(MAX_PREFLIGHT_REPORTERS + 1)
    result = preflight_policy_revision(sample_policy_trace(), context)
    assert result.status == "inconclusive"
    assert result.to_json_obj()["ok"] is False
    assert result.errors == [f"reporter_population_bound_exhausted:65>{MAX_PREFLIGHT_REPORTERS}"]
    assert result.eligible_reporter_count is None


def test_over_bound_with_malformed_context_is_rejected() -> None:
    context = sample_preflight_context()
    context["eligible_reporter_ids"] = _reporters(MAX_PREFLIGHT_REPORTERS + 1)
    context["query_id"] = "nope"
    result = preflight_policy_revision(sample_policy_trace(), context)
    assert result.status == "rejected"
    assert result.errors == ["query_id_must_be_canonical_sha256"]


# --- Exhaustive independent count check ----------------------------------------


def test_exhaustive_small_grid_matches_independent_distinct_count() -> None:
    for quorum in range(1, 7):
        trace = _trace_with_reporter_quorum(quorum)
        for population in range(0, 8):
            ids = _reporters(population)
            context = sample_preflight_context(trace)
            context["eligible_reporter_ids"] = ids
            result = preflight_policy_revision(trace, context)
            independent_ok = quorum <= len(set(ids))
            assert (result.status == "accepted") is independent_ok, (quorum, population)
            assert result.eligible_reporter_count == len(set(ids))
            assert result.min_distinct_reporters == quorum


# --- CLI -----------------------------------------------------------------------


def test_cli_preflight_accepts_sample(tmp_path: Path) -> None:
    trace = _write(tmp_path, "trace.json", json.dumps(sample_policy_trace()))
    context = _write(tmp_path, "context.json", json.dumps(sample_preflight_context()))
    code, obj = _run_cli("preflight", trace, context)
    assert code == 0
    assert obj["ok"] is True
    assert obj["status"] == "accepted"
    assert obj["premise"] == PREFLIGHT_PREMISE


def test_cli_preflight_rejects_short_population(tmp_path: Path) -> None:
    ctx = sample_preflight_context()
    ctx["eligible_reporter_ids"] = _reporters(1)
    trace = _write(tmp_path, "trace.json", json.dumps(sample_policy_trace()))
    context = _write(tmp_path, "context.json", json.dumps(ctx))
    code, obj = _run_cli("preflight", trace, context)
    assert code == 2
    assert obj["status"] == "rejected"


def test_cli_preflight_duplicate_context_key_is_inconclusive(tmp_path: Path) -> None:
    ctx = sample_preflight_context()
    text = json.dumps(ctx)
    dup = text[:-1] + ', "query_id": "' + ctx["query_id"] + '"}'
    trace = _write(tmp_path, "trace.json", json.dumps(sample_policy_trace()))
    context = _write(tmp_path, "context.json", dup)
    code, obj = _run_cli("preflight", trace, context)
    assert code == 3
    assert obj["status"] == "inconclusive"
    assert obj["ok"] is False
    assert obj["errors"] == ["preflight_load_failed:duplicate_key:query_id"]


def test_given_quorum_increase_beyond_available_reporters_then_preflight_rejects() -> None:
    trace = sample_policy_trace()
    candidate = trace["events"][2]["policy"]
    candidate["min_distinct_reporters"] = 4
    candidate["policy_id"] = content_hash(candidate, omit_key="policy_id")
    assert verify_policy_trace(trace).status == "accepted"
    result = preflight_policy_revision(trace, sample_preflight_context(trace))
    assert result.status == "rejected"
    assert result.errors == ["eligible_reporters_below_reporter_quorum:3<4"]


def test_cli_preflight_duplicate_trace_key_is_inconclusive(tmp_path: Path) -> None:
    obj = sample_policy_trace()
    text = json.dumps(obj)[:-1] + ', "query_id": ' + json.dumps(obj["query_id"]) + "}"
    trace = _write(tmp_path, "trace.json", text)
    context = _write(tmp_path, "context.json", json.dumps(sample_preflight_context()))
    code, result = _run_cli("preflight", trace, context)
    assert code == 3
    assert result["errors"] == ["preflight_load_failed:duplicate_key:query_id"]
    # Legacy verification intentionally retains its existing decoding behavior.
    assert _run_cli("verify", trace)[0] == 0


def test_cli_preflight_deep_context_is_inconclusive(tmp_path: Path) -> None:
    trace = _write(tmp_path, "trace.json", json.dumps(sample_policy_trace()))
    context = _write(tmp_path, "context.json", "[" * 2000 + "]" * 2000)
    code, result = _run_cli("preflight", trace, context)
    assert code == 3
    assert result["status"] == "inconclusive"
    assert result["ok"] is False


def test_trace_rejection_precedes_malformed_context() -> None:
    trace = sample_policy_trace()
    trace["events"][2]["policy"]["min_distinct_reporters"] = True
    result = preflight_policy_revision(trace, None)
    assert result.status == "rejected"
    assert result.errors[0] == "trace_not_accepted"


def test_cli_trace_rejection_precedes_unreadable_context(tmp_path: Path) -> None:
    obj = sample_policy_trace()
    obj["events"][2]["policy"]["min_distinct_reporters"] = True
    trace = _write(tmp_path, "trace.json", json.dumps(obj))
    code, result = _run_cli("preflight", trace, str(tmp_path / "absent.json"))
    assert code == 2
    assert result["status"] == "rejected"
    assert result["errors"][0] == "trace_not_accepted"


def test_cli_preflight_oversized_context_is_inconclusive(tmp_path: Path) -> None:
    ctx = sample_preflight_context()
    text = json.dumps(ctx)[:-1] + " " * MAX_PREFLIGHT_BYTES + "}"
    trace = _write(tmp_path, "trace.json", json.dumps(sample_policy_trace()))
    context = _write(tmp_path, "context.json", text)
    code, obj = _run_cli("preflight", trace, context)
    assert code == 3
    assert obj["status"] == "inconclusive"
    assert obj["errors"][0].startswith("preflight_load_failed:preflight_context_file_too_large:")


def test_cli_preflight_missing_context_file_is_inconclusive(tmp_path: Path) -> None:
    trace = _write(tmp_path, "trace.json", json.dumps(sample_policy_trace()))
    code, obj = _run_cli("preflight", trace, str(tmp_path / "absent.json"))
    assert code == 3
    assert obj["status"] == "inconclusive"


def test_cli_verify_json_shape_unchanged(tmp_path: Path) -> None:
    trace = _write(tmp_path, "trace.json", json.dumps(sample_policy_trace()))
    code, obj = _run_cli("verify", trace)
    assert code == 0
    assert set(obj) == {
        "schema",
        "ok",
        "status",
        "query_id",
        "active_policy_id",
        "active_policy_version",
        "published_policy_count",
        "bound_consumer_count",
        "last_epoch",
        "errors",
        "not_claimed",
    }
    assert obj["schema"] == "zenodex.oracle.query_policy_verify_result.v1"
    assert "premise" not in obj
