"""Characterization corpus for zenograph_ranking_review_campaign_index.

This locks the EXACT observable behavior (built index payload, rendered
markdown/CSV outputs, and every error type/message) of:

- build_zenograph_ranking_review_campaign_index
- render_zenograph_ranking_review_campaign_index_markdown
  (plus happy-path + schema/entries guards of the CSV renderers, which share
  the same internal helpers)

against the committed corpus JSON at
tests/integration/fixtures/zenograph_ranking_review_campaign_index_characterization_corpus.json

The corpus stores ONLY captured expected outcomes; the deterministic case
inputs live in this file (`_cases()`). Temporary campaign roots are
normalized to the `<ROOT>` placeholder so the corpus is byte-reproducible
across machines.

Regenerate (only when intentionally re-baselining behavior):

    python3 tests/integration/test_zenograph_ranking_review_campaign_index_characterization.py --regen

Regeneration is byte-reproducible: running it twice yields an identical file.
"""

from __future__ import annotations

import json
import sys
import tempfile
from base64 import b64decode
from functools import lru_cache
from pathlib import Path
from typing import Any, Callable, Mapping

import pytest

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.integration.zenograph_ranking_review_campaign_index import (  # noqa: E402
    ZENOGRAPH_AUTOTRADER_RANKING_REVIEW_CAMPAIGN_INDEX_SCHEMA,
    build_zenograph_ranking_review_campaign_index,
    render_zenograph_ranking_review_campaign_index_csv,
    render_zenograph_ranking_review_campaign_index_daily_block_reason_csv,
    render_zenograph_ranking_review_campaign_index_daily_csv,
    render_zenograph_ranking_review_campaign_index_markdown,
)

CORPUS_PATH = (
    Path(__file__).resolve().parent
    / "fixtures"
    / "zenograph_ranking_review_campaign_index_characterization_corpus.json"
)
CORPUS_SCHEMA = (
    "zenodex/zenograph-ranking-review-campaign-index-characterization-corpus/v1"
)
BUNDLE_SCHEMA = "zenodex/zenograph-autotrader-ranking-review-bundle/v1"
ROOT_PLACEHOLDER = "<ROOT>"

_ABSENT = object()

_RENDERERS: tuple[tuple[str, Callable[[Mapping[str, object]], str]], ...] = (
    ("markdown", render_zenograph_ranking_review_campaign_index_markdown),
    ("csv", render_zenograph_ranking_review_campaign_index_csv),
    ("daily_csv", render_zenograph_ranking_review_campaign_index_daily_csv),
    (
        "daily_block_reason_csv",
        render_zenograph_ranking_review_campaign_index_daily_block_reason_csv,
    ),
)
_RENDERERS_BY_NAME = dict(_RENDERERS)


# ---------------------------------------------------------------------------
# Case input builders (deterministic, defined in-code; corpus stores outputs)
# ---------------------------------------------------------------------------


def _bundle_manifest(**fields: Any) -> dict[str, Any]:
    manifest: dict[str, Any] = {"schema": BUNDLE_SCHEMA}
    manifest.update(fields)
    return manifest


def _bundle_dir(manifest: dict[str, Any] | None) -> dict[str, Any]:
    return {"kind": "dir", "manifest": manifest}


def _json_manifest(**fields: Any) -> dict[str, Any]:
    return {"json": _bundle_manifest(**fields)}


# Shared trees -------------------------------------------------------------

_SCAN_SKIPS_ZOO_TREE: dict[str, Any] = {
    "stray_file.txt": {"kind": "file", "text": "stray file, not a bundle dir\n"},
    "no_manifest": _bundle_dir(None),
    "bad_json": _bundle_dir({"text": "{not json"}),
    "json_null": _bundle_dir({"text": "null"}),
    "json_list": _bundle_dir({"json": [1, 2, 3]}),
    "json_scalar": _bundle_dir({"json": "just a string"}),
    "no_schema_key": _bundle_dir({"json": {"run_id": "skip-noschema"}}),
    "wrong_schema": _bundle_dir(
        {"json": {"schema": "zenodex/other-bundle/v1", "run_id": "skip-wrong-schema"}}
    ),
    "metadata_string": _bundle_dir(
        _json_manifest(run_id="skip-meta", metadata="oops")
    ),
    "20260601T120000Z_good": _bundle_dir(
        _json_manifest(
            run_id="good-1",
            ranking_influence_allowed=True,
            block_reason=None,
            baseline_report_path="baseline_report.json",
            gate_report_path="gate_report.json",
            summary_path="ranking_review.md",
            instructions_path="README.md",
            metadata={
                "generated_at_utc": "2026-06-01T12:00:00Z",
                "git_commit_short": "abc1234",
                "git_dirty": False,
            },
        )
    ),
}

_SORT_TREE: dict[str, Any] = {
    "20260606T000000Z_d": _bundle_dir(
        _json_manifest(
            run_id="r-z",
            ranking_influence_allowed=True,
            block_reason=None,
            metadata={
                "generated_at_utc": "2026-06-06T00:00:00Z",
                "git_commit_short": "ddd111",
                "git_dirty": False,
            },
        )
    ),
    "20260605T000000Z_c": _bundle_dir(
        _json_manifest(
            run_id="r-a",
            ranking_influence_allowed=True,
            block_reason=None,
            metadata={
                "generated_at_utc": "2026-06-05T00:00:01Z",
                "git_commit_short": "ccc111",
                "git_dirty": False,
            },
        )
    ),
    "20260605T000000Z_a": _bundle_dir(
        _json_manifest(
            run_id="r-c",
            ranking_influence_allowed=False,
            block_reason="x_reason",
            metadata={
                "generated_at_utc": "2026-06-05T00:00:00Z",
                "git_commit_short": "aaa111",
                "git_dirty": True,
            },
        )
    ),
    "20260605T000000Z_b": _bundle_dir(
        _json_manifest(
            run_id="r-b",
            ranking_influence_allowed=None,
            block_reason="",
            metadata={
                "generated_at_utc": "2026-06-05T00:00:00Z",
                "git_commit_short": "bbb111",
                "git_dirty": None,
            },
        )
    ),
    "nodate": _bundle_dir(_json_manifest(run_id="r-m")),
}

_LIMIT_TREE: dict[str, Any] = {
    "20260601T000000Z_a": _bundle_dir(
        _json_manifest(
            run_id="one",
            ranking_influence_allowed=True,
            metadata={"generated_at_utc": "2026-06-01T00:00:00Z"},
        )
    ),
    "20260602T000000Z_b": _bundle_dir(
        _json_manifest(
            run_id="two",
            ranking_influence_allowed=False,
            block_reason="why_blocked",
            metadata={"generated_at_utc": "2026-06-02T00:00:00Z"},
        )
    ),
}

_FILTER_TREE: dict[str, Any] = {
    "20260601T100000Z_fa": _bundle_dir(
        _json_manifest(
            run_id="alpha-1",
            ranking_influence_allowed=True,
            block_reason=None,
            metadata={
                "generated_at_utc": "2026-06-01T10:00:00Z",
                "git_commit_short": "abc123",
                "git_dirty": False,
            },
        )
    ),
    "20260602T100000Z_fb": _bundle_dir(
        _json_manifest(
            run_id="alpha-2",
            ranking_influence_allowed=False,
            block_reason="gate_blocked",
            metadata={
                "generated_at_utc": "2026-06-02T10:00:00Z",
                "git_commit_short": "abd456",
                "git_dirty": True,
            },
        )
    ),
    "20260603T100000Z_fc": _bundle_dir(
        _json_manifest(
            run_id="beta-1",
            ranking_influence_allowed="true",
            block_reason=None,
            metadata={
                "generated_at_utc": "2026-06-03T10:00:00Z",
                "git_commit_short": "xyz789",
                "git_dirty": True,
            },
        )
    ),
    "20260604T100000Z_fd": _bundle_dir(_json_manifest()),
}

_TS_ZOO_TREE: dict[str, Any] = {
    "20260603T101500Z": _bundle_dir(_json_manifest(run_id="ts-whole")),
    "_leading_underscore": _bundle_dir(_json_manifest(run_id="ts-leading")),
    "2026bad_x": _bundle_dir(_json_manifest(run_id="ts-bad")),
    "20260699T000000Z_x": _bundle_dir(_json_manifest(run_id="ts-invalid-date")),
    "iso_fallback": _bundle_dir(
        _json_manifest(
            run_id="ts-iso",
            metadata={"generated_at_utc": "2026-06-03T10:15:00Z"},
        )
    ),
}

_ISO_ONLY_TREE: dict[str, Any] = {
    "iso_only": _bundle_dir(
        _json_manifest(
            run_id="iso-1",
            metadata={"generated_at_utc": "2026-06-03T10:15:00Z"},
        )
    ),
}

_NO_FILTER_KWARGS: dict[str, Any] = {
    "gate_status": None,
    "run_id_prefix": None,
    "git_prefix": None,
    "dirty_state": None,
    "generated_since_utc": None,
    "generated_until_utc": None,
}


def _empty_index_payload(**overrides: Any) -> dict[str, Any]:
    payload: dict[str, Any] = {
        "schema": ZENOGRAPH_AUTOTRADER_RANKING_REVIEW_CAMPAIGN_INDEX_SCHEMA,
        "campaign_root": "/campaigns",
        "filters": dict(_NO_FILTER_KWARGS),
        "bundle_count": 0,
        "gate_status_counts": {},
        "block_reason_counts": {},
        "campaign_day_counts": {},
        "campaign_day_gate_status_counts": {},
        "block_reason_spans": {},
        "latest_gate_status": "none",
        "latest_gate_status_streak_length": 0,
        "latest_block_reason": "none",
        "latest_block_reason_streak_length": 0,
        "entries": [],
    }
    for key, value in overrides.items():
        if value is _ABSENT:
            del payload[key]
        else:
            payload[key] = value
    return payload


def _populated_index_payload(**overrides: Any) -> dict[str, Any]:
    populated: dict[str, Any] = {
        "bundle_count": 1,
        "gate_status_counts": {"unknown": 1},
        "block_reason_counts": {"none": 1},
        "campaign_day_counts": {"unknown": 1},
        "campaign_day_gate_status_counts": {"unknown": {"unknown": 1}},
        "block_reason_spans": {
            "none": {
                "count": 1,
                "first_campaign_day": "unknown",
                "last_campaign_day": "unknown",
            }
        },
        "latest_gate_status": "unknown",
        "latest_gate_status_streak_length": 1,
        "latest_block_reason": "none",
        "latest_block_reason_streak_length": 1,
        "entries": [{}],
    }
    populated.update(overrides)
    return _empty_index_payload(**populated)


def _filters(**overrides: Any) -> dict[str, Any]:
    filters = dict(_NO_FILTER_KWARGS)
    filters.update(overrides)
    return filters


def _build_case(case_id: str, **spec: Any) -> dict[str, Any]:
    case = {"case_id": case_id, "kind": "build"}
    case.update(spec)
    return case


def _render_case(
    case_id: str, payload: Any, *, renderer: str = "markdown"
) -> dict[str, Any]:
    return {
        "case_id": case_id,
        "kind": "render",
        "renderer": renderer,
        "payload": payload,
    }


def _cases() -> list[dict[str, Any]]:
    cases: list[dict[str, Any]] = []

    # --- build kwarg validation probes (campaign root never touched) -------
    cases.extend(
        [
            _build_case(
                "build_kwargs_campaign_root_str",
                root="missing",
                campaign_root_as="str",
            ),
            _build_case("build_kwargs_limit_zero", root="missing", kwargs={"limit": 0}),
            _build_case(
                "build_kwargs_limit_negative", root="missing", kwargs={"limit": -3}
            ),
            _build_case(
                "build_kwargs_limit_str", root="missing", kwargs={"limit": "5"}
            ),
            _build_case(
                "build_kwargs_limit_float", root="missing", kwargs={"limit": 1.5}
            ),
            _build_case(
                "build_kwargs_limit_bool_false",
                root="missing",
                kwargs={"limit": False},
            ),
            _build_case(
                "build_kwargs_gate_status_unknown_value",
                root="missing",
                kwargs={"gate_status": "ALLOWED"},
            ),
            _build_case(
                "build_kwargs_gate_status_bool",
                root="missing",
                kwargs={"gate_status": True},
            ),
            _build_case(
                "build_kwargs_run_id_prefix_int",
                root="missing",
                kwargs={"run_id_prefix": 7},
            ),
            _build_case(
                "build_kwargs_run_id_prefix_bool",
                root="missing",
                kwargs={"run_id_prefix": True},
            ),
            _build_case(
                "build_kwargs_git_prefix_int",
                root="missing",
                kwargs={"git_prefix": 12},
            ),
            _build_case(
                "build_kwargs_dirty_state_unknown_value",
                root="missing",
                kwargs={"dirty_state": "DIRTY"},
            ),
            _build_case(
                "build_kwargs_generated_since_int",
                root="missing",
                kwargs={"generated_since_utc": 20260101},
            ),
            _build_case(
                "build_kwargs_generated_since_iso_format",
                root="missing",
                kwargs={"generated_since_utc": "2026-01-01T00:00:00Z"},
            ),
            _build_case(
                "build_kwargs_generated_until_garbage",
                root="missing",
                kwargs={"generated_until_utc": "garbage"},
            ),
            _build_case(
                "build_kwargs_generated_until_bool",
                root="missing",
                kwargs={"generated_until_utc": True},
            ),
        ]
    )

    # --- build kwarg validation precedence (multi-fault ordering) ----------
    cases.extend(
        [
            _build_case(
                "build_kwargs_precedence_root_before_limit",
                root="missing",
                campaign_root_as="str",
                kwargs={"limit": 0},
            ),
            _build_case(
                "build_kwargs_precedence_limit_before_gate",
                root="missing",
                kwargs={"limit": 0, "gate_status": "bogus"},
            ),
            _build_case(
                "build_kwargs_precedence_gate_before_run_prefix",
                root="missing",
                kwargs={"gate_status": "bogus", "run_id_prefix": 1},
            ),
            _build_case(
                "build_kwargs_precedence_run_prefix_before_git_prefix",
                root="missing",
                kwargs={"run_id_prefix": 1, "git_prefix": 2},
            ),
            _build_case(
                "build_kwargs_precedence_git_prefix_before_dirty",
                root="missing",
                kwargs={"git_prefix": 2, "dirty_state": "bogus"},
            ),
            _build_case(
                "build_kwargs_precedence_dirty_before_since",
                root="missing",
                kwargs={"dirty_state": "bogus", "generated_since_utc": "bad"},
            ),
            _build_case(
                "build_kwargs_precedence_since_before_until",
                root="missing",
                kwargs={"generated_since_utc": "bad", "generated_until_utc": 3},
            ),
        ]
    )

    # --- build filesystem scan behavior ------------------------------------
    cases.extend(
        [
            _build_case("build_root_missing", root="missing"),
            _build_case(
                "build_root_missing_with_all_filters",
                root="missing",
                kwargs={
                    "limit": 5,
                    "gate_status": "allowed",
                    "run_id_prefix": "r",
                    "git_prefix": "g",
                    "dirty_state": "clean",
                    "generated_since_utc": "20260101T000000Z",
                    "generated_until_utc": "20261231T235959Z",
                },
            ),
            _build_case("build_root_is_file", root="file"),
            _build_case("build_root_empty_dir", tree={}),
            _build_case("build_scan_skips_zoo", tree=_SCAN_SKIPS_ZOO_TREE),
            _build_case(
                "build_manifest_is_directory",
                tree={"bundle_x": _bundle_dir({"dir": True})},
            ),
            _build_case(
                "build_manifest_non_utf8",
                tree={"bundle_y": _bundle_dir({"b64": "/w=="})},
            ),
            _build_case(
                "build_minimal_schema_only_manifest",
                tree={"nodate": _bundle_dir(_json_manifest())},
            ),
            _build_case(
                "build_metadata_null",
                tree={
                    "20260601T000000Z_x": _bundle_dir(
                        _json_manifest(run_id="m-null", metadata=None)
                    )
                },
            ),
            _build_case(
                "build_metadata_partial",
                tree={
                    "20260602T080000Z_y": _bundle_dir(
                        _json_manifest(
                            run_id="m-partial",
                            metadata={"generated_at_utc": "2026-06-02T08:00:00Z"},
                        )
                    )
                },
            ),
            _build_case("build_dir_name_timestamp_zoo", tree=_TS_ZOO_TREE),
            _build_case("build_sort_and_streaks", tree=_SORT_TREE),
            _build_case(
                "build_limit_two_truncates_aggregates",
                tree=_SORT_TREE,
                kwargs={"limit": 2},
            ),
            _build_case(
                "build_limit_bool_true_acts_as_one",
                tree=_LIMIT_TREE,
                kwargs={"limit": True},
            ),
            _build_case(
                "build_limit_exceeds_entries",
                tree=_LIMIT_TREE,
                kwargs={"limit": 10},
            ),
        ]
    )

    # --- build entry filters ------------------------------------------------
    cases.extend(
        [
            _build_case(
                "build_filter_gate_allowed",
                tree=_FILTER_TREE,
                kwargs={"gate_status": "allowed"},
            ),
            _build_case(
                "build_filter_gate_blocked",
                tree=_FILTER_TREE,
                kwargs={"gate_status": "blocked"},
            ),
            _build_case(
                "build_filter_run_prefix_alpha",
                tree=_FILTER_TREE,
                kwargs={"run_id_prefix": "alpha"},
            ),
            _build_case(
                "build_filter_run_prefix_empty",
                tree=_FILTER_TREE,
                kwargs={"run_id_prefix": ""},
            ),
            _build_case(
                "build_filter_git_prefix_ab",
                tree=_FILTER_TREE,
                kwargs={"git_prefix": "ab"},
            ),
            _build_case(
                "build_filter_dirty_clean",
                tree=_FILTER_TREE,
                kwargs={"dirty_state": "clean"},
            ),
            _build_case(
                "build_filter_dirty_dirty",
                tree=_FILTER_TREE,
                kwargs={"dirty_state": "dirty"},
            ),
            _build_case(
                "build_filter_since",
                tree=_FILTER_TREE,
                kwargs={"generated_since_utc": "20260602T100000Z"},
            ),
            _build_case(
                "build_filter_until",
                tree=_FILTER_TREE,
                kwargs={"generated_until_utc": "20260602T100000Z"},
            ),
            _build_case(
                "build_filter_since_until_window",
                tree=_FILTER_TREE,
                kwargs={
                    "generated_since_utc": "20260602T000000Z",
                    "generated_until_utc": "20260602T235959Z",
                },
            ),
            _build_case(
                "build_filter_combined_all",
                tree=_FILTER_TREE,
                kwargs={
                    "gate_status": "blocked",
                    "run_id_prefix": "alpha",
                    "git_prefix": "ab",
                    "dirty_state": "dirty",
                    "generated_since_utc": "20260602T000000Z",
                    "generated_until_utc": "20260602T235959Z",
                },
            ),
            _build_case(
                "build_filter_since_excludes_timestampless",
                tree={
                    "nodate2": _bundle_dir(_json_manifest(run_id="no-ts")),
                    "20260601T000000Z_ok": _bundle_dir(
                        _json_manifest(run_id="with-ts")
                    ),
                },
                kwargs={"generated_since_utc": "20000101T000000Z"},
            ),
            _build_case(
                "build_filter_since_iso_fallback_included",
                tree=_ISO_ONLY_TREE,
                kwargs={"generated_since_utc": "20000101T000000Z"},
            ),
            _build_case(
                "build_filter_since_iso_fallback_excluded_quirk",
                tree=_ISO_ONLY_TREE,
                kwargs={"generated_since_utc": "20260101T000000Z"},
            ),
        ]
    )

    # --- build poisoned manifest fields ------------------------------------
    cases.extend(
        [
            _build_case(
                "build_block_reason_int_raises",
                tree={
                    "20260601T000000Z_p1": _bundle_dir(
                        _json_manifest(run_id="poison-block", block_reason=7)
                    )
                },
            ),
            _build_case(
                "build_run_id_int_markdown_csv_raise",
                tree={
                    "20260601T000000Z_p2": _bundle_dir(
                        _json_manifest(
                            run_id=123,
                            ranking_influence_allowed=True,
                            metadata={"generated_at_utc": "2026-06-01T00:00:00Z"},
                        )
                    )
                },
            ),
            _build_case(
                "build_git_commit_int_markdown_csv_raise",
                tree={
                    "20260601T000000Z_p3": _bundle_dir(
                        _json_manifest(
                            run_id="poison-git",
                            metadata={
                                "generated_at_utc": "2026-06-01T00:00:00Z",
                                "git_commit_short": 99,
                            },
                        )
                    )
                },
            ),
            _build_case(
                "build_git_dirty_string_renders_unknown",
                tree={
                    "20260601T000000Z_p4": _bundle_dir(
                        _json_manifest(
                            run_id="dirty-str",
                            metadata={"git_dirty": "yes"},
                        )
                    )
                },
            ),
            _build_case(
                "build_allowed_int_one_renders_unknown",
                tree={
                    "20260601T000000Z_p5": _bundle_dir(
                        _json_manifest(
                            run_id="allowed-int", ranking_influence_allowed=1
                        )
                    )
                },
            ),
        ]
    )

    # --- markdown renderer payload validation probes ------------------------
    cases.extend(
        [
            _render_case("render_md_payload_list", []),
            _render_case("render_md_payload_string", "not-a-mapping"),
            _render_case("render_md_schema_missing", {}),
            _render_case("render_md_schema_wrong", {"schema": "zenodex/other/v1"}),
            _render_case(
                "render_md_campaign_root_missing",
                _empty_index_payload(campaign_root=_ABSENT),
            ),
            _render_case(
                "render_md_campaign_root_int", _empty_index_payload(campaign_root=5)
            ),
            _render_case(
                "render_md_bundle_count_str", _empty_index_payload(bundle_count="3")
            ),
            _render_case(
                "render_md_bundle_count_bool", _empty_index_payload(bundle_count=True)
            ),
            _render_case(
                "render_md_filters_missing", _empty_index_payload(filters=_ABSENT)
            ),
            _render_case(
                "render_md_filters_string", _empty_index_payload(filters="f")
            ),
            _render_case(
                "render_md_entries_missing", _empty_index_payload(entries=_ABSENT)
            ),
            _render_case("render_md_entries_dict", _empty_index_payload(entries={})),
            _render_case(
                "render_md_gate_status_counts_list",
                _empty_index_payload(gate_status_counts=[]),
            ),
            _render_case(
                "render_md_block_reason_counts_int",
                _empty_index_payload(block_reason_counts=3),
            ),
            _render_case(
                "render_md_campaign_day_counts_null",
                _empty_index_payload(campaign_day_counts=None),
            ),
            _render_case(
                "render_md_day_gate_counts_string",
                _empty_index_payload(campaign_day_gate_status_counts="s"),
            ),
            _render_case(
                "render_md_block_reason_spans_list",
                _empty_index_payload(block_reason_spans=[]),
            ),
            _render_case(
                "render_md_latest_gate_status_missing",
                _empty_index_payload(latest_gate_status=_ABSENT),
            ),
            _render_case(
                "render_md_latest_gate_streak_string",
                _empty_index_payload(latest_gate_status_streak_length="2"),
            ),
            _render_case(
                "render_md_latest_block_reason_int",
                _empty_index_payload(latest_block_reason=7),
            ),
            _render_case(
                "render_md_latest_block_streak_null",
                _empty_index_payload(latest_block_reason_streak_length=None),
            ),
        ]
    )

    # --- markdown renderer validation precedence ----------------------------
    cases.extend(
        [
            _render_case(
                "render_md_precedence_schema_before_campaign_root",
                {"schema": "zenodex/other/v1", "campaign_root": 5},
            ),
            _render_case(
                "render_md_precedence_campaign_root_before_bundle_count",
                _empty_index_payload(campaign_root=5, bundle_count="x"),
            ),
            _render_case(
                "render_md_precedence_filters_before_entries",
                _empty_index_payload(filters="f", entries="e"),
            ),
            _render_case(
                "render_md_precedence_entries_before_gate_counts",
                _empty_index_payload(entries="e", gate_status_counts=[]),
            ),
        ]
    )

    # --- markdown renderer behavior probes ----------------------------------
    cases.extend(
        [
            _render_case("render_md_empty_no_filters", _empty_index_payload()),
            _render_case(
                "render_md_empty_with_one_filter",
                _empty_index_payload(filters=_filters(gate_status="allowed")),
            ),
            _render_case(
                "render_md_filter_empty_string_renders_section_with_none",
                _empty_index_payload(filters=_filters(run_id_prefix="")),
            ),
            _render_case(
                "render_md_filter_value_int_raises",
                _empty_index_payload(filters=_filters(gate_status=5)),
            ),
            _render_case(
                "render_md_unsorted_inputs_resorted",
                _empty_index_payload(
                    bundle_count=3,
                    gate_status_counts={"zz-gate": 1, "aa-gate": 2},
                    block_reason_counts={"b-reason": 1, "a-reason": 2},
                    campaign_day_counts={"20260102": 1, "20260101": 2},
                    campaign_day_gate_status_counts={
                        "20260102": {},
                        "20260101": {"b-gate": 1, "a-gate": 1},
                    },
                    block_reason_spans={
                        "z-span": {
                            "count": 1,
                            "first_campaign_day": "20260101",
                            "last_campaign_day": "20260102",
                        },
                        "a-span": {
                            "count": 2,
                            "first_campaign_day": "20260101",
                            "last_campaign_day": "20260101",
                        },
                    },
                    latest_gate_status="aa-gate",
                    latest_gate_status_streak_length=2,
                    latest_block_reason="a-reason",
                    latest_block_reason_streak_length=3,
                    entries=[
                        {
                            "run_id": "row-1",
                            "generated_at_utc": "2026-01-01T00:00:00Z",
                            "ranking_influence_allowed": True,
                            "block_reason": None,
                            "git_commit_short": "c0ffee1",
                            "git_dirty": False,
                        },
                        {"run_id": "row-2"},
                    ],
                ),
            ),
            _render_case(
                "render_md_day_missing_from_gate_counts_raises",
                _populated_index_payload(
                    campaign_day_counts={"20260101": 1},
                    campaign_day_gate_status_counts={},
                ),
            ),
            _render_case(
                "render_md_gate_count_value_bool_raises",
                _populated_index_payload(gate_status_counts={"allowed": True}),
            ),
            _render_case(
                "render_md_block_reason_count_value_str_raises",
                _populated_index_payload(block_reason_counts={"x": "1"}),
            ),
            _render_case(
                "render_md_day_count_value_float_raises",
                _populated_index_payload(
                    campaign_day_counts={"20260101": 1.0},
                    campaign_day_gate_status_counts={"20260101": {"unknown": 1}},
                ),
            ),
            _render_case(
                "render_md_day_gate_inner_value_str_raises",
                _populated_index_payload(
                    campaign_day_counts={"20260101": 1},
                    campaign_day_gate_status_counts={"20260101": {"allowed": "1"}},
                ),
            ),
            _render_case(
                "render_md_span_entry_not_mapping_raises",
                _populated_index_payload(block_reason_spans={"x": 3}),
            ),
            _render_case(
                "render_md_span_count_missing_raises",
                _populated_index_payload(
                    block_reason_spans={
                        "x": {"first_campaign_day": "a", "last_campaign_day": "b"}
                    }
                ),
            ),
            _render_case(
                "render_md_span_first_day_int_raises",
                _populated_index_payload(
                    block_reason_spans={
                        "x": {
                            "count": 1,
                            "first_campaign_day": 1,
                            "last_campaign_day": "b",
                        }
                    }
                ),
            ),
            _render_case(
                "render_md_span_last_day_missing_raises",
                _populated_index_payload(
                    block_reason_spans={"x": {"count": 1, "first_campaign_day": "a"}}
                ),
            ),
            _render_case(
                "render_md_entry_not_mapping_raises",
                _populated_index_payload(entries=["not-a-mapping"]),
            ),
            _render_case(
                "render_md_entry_all_fields_missing_row_unknowns",
                _populated_index_payload(),
            ),
            _render_case(
                "render_md_entry_field_type_zoo",
                _populated_index_payload(
                    entries=[
                        {
                            "run_id": "ok-1",
                            "generated_at_utc": None,
                            "ranking_influence_allowed": 0,
                            "block_reason": "",
                            "git_commit_short": None,
                            "git_dirty": "y",
                        }
                    ]
                ),
            ),
        ]
    )

    # --- csv renderer guard probes (shared helpers) --------------------------
    cases.extend(
        [
            _render_case(
                "render_csv_schema_wrong", {"schema": "zenodex/other/v1"}, renderer="csv"
            ),
            _render_case(
                "render_csv_entries_dict",
                _empty_index_payload(entries={}),
                renderer="csv",
            ),
        ]
    )

    return cases


CASES = _cases()
CASE_IDS = [case["case_id"] for case in CASES]


# ---------------------------------------------------------------------------
# Corpus capture machinery
# ---------------------------------------------------------------------------


def _materialize_tree(campaign_root: Path, tree: Mapping[str, Any]) -> None:
    for name, node in tree.items():
        child = campaign_root / name
        if node["kind"] == "file":
            child.write_text(node["text"], encoding="utf-8")
            continue
        if node["kind"] != "dir":
            raise ValueError(f"unknown tree node kind: {node['kind']!r}")
        child.mkdir()
        manifest = node.get("manifest")
        if manifest is None:
            continue
        manifest_path = child / "manifest.json"
        if "json" in manifest:
            manifest_path.write_text(
                json.dumps(manifest["json"], sort_keys=True), encoding="utf-8"
            )
        elif "text" in manifest:
            manifest_path.write_text(manifest["text"], encoding="utf-8")
        elif "b64" in manifest:
            manifest_path.write_bytes(b64decode(manifest["b64"]))
        elif manifest.get("dir") is True:
            manifest_path.mkdir()
        else:
            raise ValueError(f"unknown manifest spec: {manifest!r}")


def _normalize_text(text: str, root_str: str | None) -> str:
    if root_str:
        return text.replace(root_str, ROOT_PLACEHOLDER)
    return text


def _normalize_value(value: Any, root_str: str | None) -> Any:
    if isinstance(value, str):
        return _normalize_text(value, root_str)
    if isinstance(value, list):
        return [_normalize_value(item, root_str) for item in value]
    if isinstance(value, dict):
        return {
            _normalize_value(key, root_str): _normalize_value(item, root_str)
            for key, item in value.items()
        }
    return value


def _capture(
    fn: Callable[[], Any], root_str: str | None
) -> tuple[dict[str, Any] | None, Any]:
    try:
        value = fn()
    except Exception as exc:  # noqa: BLE001 - characterization captures any failure
        return (
            {
                "outcome": "error",
                "error_type": type(exc).__name__,
                "error_message": _normalize_text(str(exc), root_str),
            },
            None,
        )
    return None, value


def _run_build_case(case: Mapping[str, Any], base: Path) -> dict[str, Any]:
    base.mkdir(parents=True, exist_ok=True)
    campaign_root = base / "campaign"
    root_mode = case.get("root", "dir")
    if root_mode == "dir":
        campaign_root.mkdir()
        _materialize_tree(campaign_root, case.get("tree", {}))
    elif root_mode == "file":
        campaign_root.write_text("not a directory\n", encoding="utf-8")
    elif root_mode != "missing":
        raise ValueError(f"unknown root mode: {root_mode!r}")

    root_str = str(campaign_root)
    root_arg: Any = (
        root_str if case.get("campaign_root_as") == "str" else campaign_root
    )
    kwargs = dict(case.get("kwargs", {}))

    error, index = _capture(
        lambda: build_zenograph_ranking_review_campaign_index(
            campaign_root=root_arg, **kwargs
        ),
        root_str,
    )
    if error is not None:
        return {"build": error}

    result: dict[str, Any] = {
        "build": {
            "outcome": "ok",
            "index_json": json.dumps(
                _normalize_value(index, root_str), ensure_ascii=True
            ),
        }
    }
    for name, renderer in _RENDERERS:
        render_error, text = _capture(lambda r=renderer: r(index), root_str)
        if render_error is not None:
            result[name] = render_error
        else:
            result[name] = {
                "outcome": "ok",
                "output": _normalize_text(text, root_str),
            }
    return result


def _run_render_case(case: Mapping[str, Any]) -> dict[str, Any]:
    renderer = _RENDERERS_BY_NAME[case["renderer"]]
    error, text = _capture(lambda: renderer(case["payload"]), None)
    if error is not None:
        return {case["renderer"]: error}
    return {case["renderer"]: {"outcome": "ok", "output": text}}


def _run_case(case: Mapping[str, Any], base: Path) -> dict[str, Any]:
    if case["kind"] == "build":
        return _run_build_case(case, base)
    if case["kind"] == "render":
        return _run_render_case(case)
    raise ValueError(f"unknown case kind: {case['kind']!r}")


def _canonical_corpus_bytes(corpus: Mapping[str, Any]) -> bytes:
    return (
        json.dumps(corpus, indent=2, sort_keys=True, ensure_ascii=True) + "\n"
    ).encode("utf-8")


@lru_cache(maxsize=1)
def _load_corpus() -> dict[str, Any]:
    return json.loads(CORPUS_PATH.read_text(encoding="utf-8"))


# ---------------------------------------------------------------------------
# Tests
# ---------------------------------------------------------------------------


def test_case_ids_unique() -> None:
    assert len(CASE_IDS) == len(set(CASE_IDS))


def test_corpus_in_sync_with_cases() -> None:
    corpus = _load_corpus()
    assert corpus["schema"] == CORPUS_SCHEMA
    assert corpus["case_count"] == len(CASES)
    assert set(corpus["cases"]) == set(CASE_IDS)


def test_corpus_file_is_canonically_serialized() -> None:
    raw = CORPUS_PATH.read_bytes()
    assert raw == _canonical_corpus_bytes(json.loads(raw.decode("utf-8")))


@pytest.mark.parametrize("case", CASES, ids=CASE_IDS)
def test_replay_matches_corpus(case: dict[str, Any], tmp_path: Path) -> None:
    expected = _load_corpus()["cases"][case["case_id"]]
    actual = _run_case(case, tmp_path)
    assert actual == expected


def _iter_corpus_outcomes() -> list[dict[str, Any]]:
    outcomes: list[dict[str, Any]] = []
    for expected in _load_corpus()["cases"].values():
        outcomes.extend(expected.values())
    return outcomes


# Every distinct error surface the two target functions can produce must stay
# represented in the corpus.  (type, exact message) for module-raised errors;
# (type, substring) for OS/codec errors whose full text embeds runtime detail.
_REQUIRED_EXACT_ERRORS: tuple[tuple[str, str], ...] = (
    ("TypeError", "campaign_root must be a Path"),
    ("ValueError", "limit must be a positive integer when present"),
    ("ValueError", "gate_status must be 'allowed' or 'blocked' when present"),
    ("TypeError", "run_id_prefix must be a string when present"),
    ("TypeError", "git_prefix must be a string when present"),
    ("ValueError", "dirty_state must be 'clean' or 'dirty' when present"),
    ("TypeError", "generated UTC filters must be strings when present"),
    ("ValueError", "generated UTC filters must use YYYYMMDDTHHMMSSZ format"),
    ("TypeError", "expected a string or null"),
    ("TypeError", "payload must be a mapping"),
    ("ValueError", "unsupported campaign index schema"),
    ("TypeError", "campaign_root must be a string"),
    ("TypeError", "bundle_count must be an int"),
    ("TypeError", "filters must be a mapping"),
    ("TypeError", "entries must be a list"),
    ("TypeError", "gate_status_counts must be a mapping"),
    ("TypeError", "block_reason_counts must be a mapping"),
    ("TypeError", "campaign_day_counts must be a mapping"),
    ("TypeError", "campaign_day_gate_status_counts must be a mapping"),
    ("TypeError", "block_reason_spans must be a mapping"),
    ("TypeError", "latest_gate_status must be a string"),
    ("TypeError", "latest_gate_status_streak_length must be an int"),
    ("TypeError", "latest_block_reason must be a string"),
    ("TypeError", "latest_block_reason_streak_length must be an int"),
    ("TypeError", "campaign_day_gate_status_counts entries must be mappings"),
    ("TypeError", "gate_status_counts.allowed must be an int"),
    ("TypeError", "block_reason_counts.x must be an int"),
    ("TypeError", "campaign_day_counts.20260101 must be an int"),
    ("TypeError", "campaign_day_gate_status_counts.20260101.allowed must be an int"),
    ("TypeError", "block_reason_spans entries must be mappings"),
    ("TypeError", "block_reason_spans.x.count must be an int"),
    ("TypeError", "block_reason_spans.x.first_campaign_day must be a string"),
    ("TypeError", "block_reason_spans.x.last_campaign_day must be a string"),
    ("TypeError", "entries must contain objects"),
)

_REQUIRED_ERROR_SUBSTRINGS: tuple[tuple[str, str], ...] = (
    ("NotADirectoryError", "Not a directory"),
    ("IsADirectoryError", "Is a directory"),
    ("UnicodeDecodeError", "codec can't decode"),
)

_REQUIRED_MARKDOWN_MARKERS: tuple[str, ...] = (
    "# ZenoGraph Ranking Review Campaign Index",
    "No bundle manifests found.",
    "## Filters",
    "## Summary",
    "## Campaign Day Trends",
    "## Block Reason Spans",
    "| `unknown` | `unknown` | `unknown` | `none` | `unknown` | `unknown` |",
    "- Latest gate status streak: `allowed` x `2`",
    "- Latest block reason streak: `none` x `2`",
    "- Run ID prefix: `none`",
    "| `none` |",
)


def test_branch_outcome_coverage_guard() -> None:
    outcomes = _iter_corpus_outcomes()
    errors = {
        (outcome["error_type"], outcome["error_message"])
        for outcome in outcomes
        if outcome["outcome"] == "error"
    }
    for required in _REQUIRED_EXACT_ERRORS:
        assert required in errors, f"corpus lost error branch: {required}"
    for error_type, fragment in _REQUIRED_ERROR_SUBSTRINGS:
        assert any(
            current_type == error_type and fragment in message
            for current_type, message in errors
        ), f"corpus lost error branch: ({error_type}, *{fragment}*)"

    cases = _load_corpus()["cases"]
    markdown_ok = "\n\x00\n".join(
        expected["markdown"]["output"]
        for expected in cases.values()
        if "markdown" in expected and expected["markdown"]["outcome"] == "ok"
    )
    for marker in _REQUIRED_MARKDOWN_MARKERS:
        assert marker in markdown_ok, f"corpus lost markdown branch: {marker!r}"
    assert any(
        "## Filters" not in expected["markdown"]["output"]
        and "## Summary" in expected["markdown"]["output"]
        for expected in cases.values()
        if "markdown" in expected and expected["markdown"]["outcome"] == "ok"
    ), "corpus lost: populated markdown without a Filters section"

    build_ok_counts = [
        json.loads(expected["build"]["index_json"])["bundle_count"]
        for expected in cases.values()
        if "build" in expected and expected["build"]["outcome"] == "ok"
    ]
    assert 0 in build_ok_counts, "corpus lost: empty build case"
    assert any(count >= 5 for count in build_ok_counts), "corpus lost: rich build case"
    precedence_ids = [case_id for case_id in cases if "precedence" in case_id]
    assert len(precedence_ids) >= 6, "corpus lost: precedence/multi-fault probes"


def test_all_module_functions_executed_by_corpus(tmp_path: Path) -> None:
    """Guard: replaying the corpus must execute every function in the module.

    This keeps the corpus honest after refactors: any newly extracted helper
    that the corpus never reaches (or a dead helper left behind) fails here.
    """
    import inspect

    module = sys.modules[build_zenograph_ranking_review_campaign_index.__module__]
    module_functions = {
        name
        for name, fn in inspect.getmembers(module, inspect.isfunction)
        if fn.__module__ == module.__name__
    }
    module_file = module.__file__
    executed: set[str] = set()

    def profiler(frame: Any, event: str, arg: Any) -> None:
        if event == "call" and frame.f_code.co_filename == module_file:
            executed.add(frame.f_code.co_name)

    previous = sys.getprofile()
    sys.setprofile(profiler)
    try:
        for position, case in enumerate(CASES):
            _run_case(case, tmp_path / f"case_{position}")
    finally:
        sys.setprofile(previous)

    missing = module_functions - executed
    assert not missing, f"corpus never executes module functions: {sorted(missing)}"


# ---------------------------------------------------------------------------
# --regen entry point
# ---------------------------------------------------------------------------


def _regenerate() -> None:
    captured: dict[str, dict[str, Any]] = {}
    for case in CASES:
        with tempfile.TemporaryDirectory(
            prefix="zenograph_index_corpus_"
        ) as temp_dir:
            captured[case["case_id"]] = _run_case(case, Path(temp_dir))
    corpus = {
        "schema": CORPUS_SCHEMA,
        "case_count": len(captured),
        "cases": captured,
    }
    CORPUS_PATH.parent.mkdir(parents=True, exist_ok=True)
    CORPUS_PATH.write_bytes(_canonical_corpus_bytes(corpus))
    print(
        f"wrote {CORPUS_PATH.relative_to(ROOT)} with {len(captured)} cases",
        file=sys.stderr,
    )


if __name__ == "__main__":
    if sys.argv[1:] == ["--regen"]:
        _regenerate()
    else:
        print(__doc__, file=sys.stderr)
        raise SystemExit(2)
