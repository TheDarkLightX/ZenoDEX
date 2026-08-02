"""Deterministic K05 bypass-mutation campaign over the K01 entrypoint set."""

from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import cast

_ROOT = Path(__file__).resolve().parents[1]
if str(_ROOT) not in sys.path:
    sys.path.insert(0, str(_ROOT))

from experiments.fcis_m6_d08_combined_anf_check import build_instance  # noqa: E402
from src.core import fcis_m6_d08_combined_anf as d08  # noqa: E402
from src.core.fcis_m6_d08_combined_anf import verify_combined_anf_v1  # noqa: E402
from src.core.fcis_m6_k02_commit_port import (  # noqa: E402
    K02PublicationRequestV1,
    initial_port_state_v1,
    unique_commit_port_v1,
)
from src.core.fcis_m6_k05_bypass_mutants import (  # noqa: E402
    K05KillCodeV1,
    K05MutantV1,
    run_mutation_matrix_v1,
)
from tools.check_fcis_m6_k03_static_no_bypass import run_static_scan  # noqa: E402

_K01_VECTOR = _ROOT / "docs/research/m6_tasks/TASK_K01_VALUE_MOVING_ENTRYPOINT_INVENTORY_V1.json"


def _entrypoint_ids() -> tuple[str, ...]:
    value = json.loads(_K01_VECTOR.read_text(encoding="utf-8"))
    if type(value) is not dict or type(value.get("entrypoints")) is not list:
        raise AssertionError("K01 vector is malformed")
    rows = cast(list[object], value["entrypoints"])
    ids: list[str] = []
    for index, row in enumerate(rows):
        if type(row) is not dict or type(row.get("publisher_id")) is not str:
            raise AssertionError(f"K01 entrypoint {index} is malformed")
        ids.append(cast(str, row["publisher_id"]))
    return tuple(ids)


def _request() -> K02PublicationRequestV1:
    result = verify_combined_anf_v1(build_instance())
    if type(result) is not d08.D08CombinedANFAcceptV1:
        raise AssertionError(f"expected verified D08 fixture, got {result!r}")
    return K02PublicationRequestV1(anf_accept=result)


def run_checks() -> None:
    static_report = run_static_scan()
    if static_report["ok"] is not True:
        raise AssertionError(f"K05 requires a clean K03 static slice: {static_report}")
    ids = _entrypoint_ids()
    if len(ids) != 15:
        raise AssertionError(f"expected 15 K01 entrypoints, found {len(ids)}")
    if ids != tuple(sorted(ids, key=lambda item: item.encode("utf-8"))):
        raise AssertionError("K01 entrypoint IDs are not canonical")
    port = unique_commit_port_v1()
    request = _request()
    state = initial_port_state_v1(request.expected_pre_state_root)
    results = run_mutation_matrix_v1(ids, port, state, request)
    if len(results) != 90:
        raise AssertionError(f"expected 90 K05 mutation results, found {len(results)}")
    expected_codes = {
        K05MutantV1.RETURN_SUCCESS_WITHOUT_COMMIT: K05KillCodeV1.MISSING_COMMIT_EVIDENCE,
        K05MutantV1.DIRECT_STATE_WRITE: K05KillCodeV1.DIRECT_STATE_WRITE_NOT_AT_PORT,
        K05MutantV1.DIRECT_OUTBOX_WRITE: K05KillCodeV1.OUTBOX_REQUIRES_COMMITTED_HISTORY,
        K05MutantV1.SKIP_PROOF_CONTEXT: K05KillCodeV1.ANF_WITNESS_REQUIRED,
        K05MutantV1.SKIP_CURRENT_ROOT_CAS: K05KillCodeV1.CURRENT_ROOT_CAS_REQUIRED,
        K05MutantV1.USE_LEGACY_WRITER: K05KillCodeV1.LEGACY_PUBLISHER_REJECTED,
    }
    for result in results:
        if not result.killed or result.kill_code is not expected_codes[result.mutant]:
            raise AssertionError(f"K05 mutant was not killed by its named invariant: {result}")
    for entrypoint_id in ids:
        rows = tuple(result for result in results if result.entrypoint_id == entrypoint_id)
        if len(rows) != len(K05MutantV1):
            raise AssertionError(f"entrypoint {entrypoint_id} lacks complete mutant coverage")


if __name__ == "__main__":
    run_checks()
    print("K05_BYPASS_MUTATION_MATCH", "entrypoints=15", "mutants=90")
