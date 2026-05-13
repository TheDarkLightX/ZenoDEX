"""Bounded price-grid table verifier for UPBA optimality evidence.

This module is the runtime bridge for the bounded price-grid Lean theorem in
`Proofs/UniformBatchOptimality.lean`.

The scorer is deliberately scoped: single-pool exact-in UPBA, full-fill-or-reject
per grid price. It does not claim global optimality for arbitrary partial-fill
solvers or unbounded rational prices.
"""

from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass
from typing import Any, Mapping, Sequence

from ..state.balances import BalanceTable
from ..state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex
from ..state.intents import Intent, IntentKind
from ..state.pools import CURVE_TAG_CPMM, PoolState, PoolStatus
from .cpmm import compute_fee_total
from .domain_limits import DEX_POOL_RESERVE_MAX, DEX_SWAP_AMOUNT_MAX
from .uniform_batch_clearing import (
    UNIFORM_BATCH_CERTIFICATE_SCHEMA_V1,
    UNIFORM_BATCH_OUTPUT_AMOUNT_MAX,
    UNIFORM_BATCH_POLICY_V1_ID,
    UniformBatchCertificateV1,
    uniform_batch_certificate_hash,
    uniform_batch_intent_set_hash,
    uniform_batch_pool_state_hash,
    verify_uniform_batch_certificate_v1,
)

UPBA_PRICE_GRID_CONFIG_SCHEMA_V1 = "zenodex/upba_price_grid_config/v1"
UPBA_PRICE_GRID_ROW_SCHEMA_V1 = "zenodex/upba_price_grid_row/v1"
UPBA_PRICE_GRID_WITNESS_SCHEMA_V1 = "zenodex/upba_price_grid_witness/v1"
UPBA_PRICE_GRID_TABLE_ROOT_SCHEMA_V1 = "zenodex/upba_price_grid_table/v1"
UPBA_PRICE_GRID_CANDIDATE_ID_SCHEMA_V1 = "zenodex/upba_price_grid_candidate_id/v1"
UPBA_PRICE_GRID_SCORE_FUNCTION_ID_V1 = "zenodex/upba_price_grid/full_fill_exact_in_limit/v1"
UPBA_PRICE_GRID_MAX_ROWS = 4_096

_CONFIG_KEYS = frozenset(
    {
        "schema",
        "settlement_id",
        "pool_id",
        "policy_id",
        "max_price_num",
        "max_price_den",
        "score_function_id",
        "candidate_table_root",
        "row_count",
    }
)
_ROW_KEYS = frozenset(
    {
        "schema",
        "settlement_id",
        "price_num",
        "price_den",
        "candidate_id",
        "valid_price_ok",
        "score_recomputed_ok",
        "volume",
        "surplus",
        "winner_row_ok",
        "dominated_by_winner_ok",
    }
)
_WITNESS_KEYS = frozenset(
    {
        "schema",
        "settlement_id",
        "uniform_batch_certificate_hash",
        "candidate_table_root",
        "winner_candidate_id",
        "winner_price_num",
        "winner_price_den",
        "volume_upper",
        "surplus_upper_at_winner_volume",
        "table_complete_ok",
        "certificate_bound_ok",
        "global_grid_optimality_ok",
    }
)


@dataclass(frozen=True)
class UniformBatchPriceGridScoreV1:
    valid_price_ok: bool
    volume: int
    surplus: int


@dataclass(frozen=True)
class UniformBatchPriceGridConfigV1:
    settlement_id: str
    pool_id: str
    policy_id: str
    max_price_num: int
    max_price_den: int
    score_function_id: str
    candidate_table_root: str
    row_count: int
    schema: str = UPBA_PRICE_GRID_CONFIG_SCHEMA_V1

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema": self.schema,
            "settlement_id": self.settlement_id,
            "pool_id": self.pool_id,
            "policy_id": self.policy_id,
            "max_price_num": int(self.max_price_num),
            "max_price_den": int(self.max_price_den),
            "score_function_id": self.score_function_id,
            "candidate_table_root": self.candidate_table_root,
            "row_count": int(self.row_count),
        }

    @classmethod
    def from_obj(cls, obj: Mapping[str, Any]) -> "UniformBatchPriceGridConfigV1":
        _reject_unknown_keys(obj, allowed=_CONFIG_KEYS, name="price_grid.config")
        schema = _require_str(obj.get("schema"), name="config.schema")
        if schema != UPBA_PRICE_GRID_CONFIG_SCHEMA_V1:
            raise ValueError("unsupported price grid config schema")
        score_function_id = _require_str(obj.get("score_function_id"), name="config.score_function_id")
        if score_function_id != UPBA_PRICE_GRID_SCORE_FUNCTION_ID_V1:
            raise ValueError("unsupported price grid score_function_id")
        policy_id = _require_str(obj.get("policy_id"), name="config.policy_id")
        if policy_id != UNIFORM_BATCH_POLICY_V1_ID:
            raise ValueError("price grid verifier supports UPBA v1 full-fill policy only")
        return cls(
            settlement_id=_require_str(obj.get("settlement_id"), name="config.settlement_id"),
            pool_id=_require_str(obj.get("pool_id"), name="config.pool_id"),
            policy_id=policy_id,
            max_price_num=_require_nonnegative_int(obj.get("max_price_num"), name="config.max_price_num"),
            max_price_den=_require_nonnegative_int(obj.get("max_price_den"), name="config.max_price_den"),
            score_function_id=score_function_id,
            candidate_table_root=_require_sha256_hex(
                obj.get("candidate_table_root"),
                name="config.candidate_table_root",
            ),
            row_count=_require_nonnegative_int(obj.get("row_count"), name="config.row_count"),
            schema=schema,
        )


@dataclass(frozen=True)
class UniformBatchPriceGridRowV1:
    settlement_id: str
    price_num: int
    price_den: int
    candidate_id: str
    valid_price_ok: bool
    score_recomputed_ok: bool
    volume: int
    surplus: int
    winner_row_ok: bool
    dominated_by_winner_ok: bool
    schema: str = UPBA_PRICE_GRID_ROW_SCHEMA_V1

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema": self.schema,
            "settlement_id": self.settlement_id,
            "price_num": int(self.price_num),
            "price_den": int(self.price_den),
            "candidate_id": self.candidate_id,
            "valid_price_ok": bool(self.valid_price_ok),
            "score_recomputed_ok": bool(self.score_recomputed_ok),
            "volume": int(self.volume),
            "surplus": int(self.surplus),
            "winner_row_ok": bool(self.winner_row_ok),
            "dominated_by_winner_ok": bool(self.dominated_by_winner_ok),
        }

    @classmethod
    def from_obj(cls, obj: Mapping[str, Any]) -> "UniformBatchPriceGridRowV1":
        _reject_unknown_keys(obj, allowed=_ROW_KEYS, name="price_grid.row")
        schema = _require_str(obj.get("schema"), name="row.schema")
        if schema != UPBA_PRICE_GRID_ROW_SCHEMA_V1:
            raise ValueError("unsupported price grid row schema")
        return cls(
            settlement_id=_require_str(obj.get("settlement_id"), name="row.settlement_id"),
            price_num=_require_nonnegative_int(obj.get("price_num"), name="row.price_num"),
            price_den=_require_nonnegative_int(obj.get("price_den"), name="row.price_den"),
            candidate_id=_require_sha256_hex(obj.get("candidate_id"), name="row.candidate_id"),
            valid_price_ok=_require_bool(obj.get("valid_price_ok"), name="row.valid_price_ok"),
            score_recomputed_ok=_require_bool(obj.get("score_recomputed_ok"), name="row.score_recomputed_ok"),
            volume=_require_nonnegative_int(
                obj.get("volume"),
                name="row.volume",
                maximum=UNIFORM_BATCH_OUTPUT_AMOUNT_MAX * UPBA_PRICE_GRID_MAX_ROWS,
            ),
            surplus=_require_nonnegative_int(
                obj.get("surplus"),
                name="row.surplus",
                maximum=UNIFORM_BATCH_OUTPUT_AMOUNT_MAX * DEX_SWAP_AMOUNT_MAX * UPBA_PRICE_GRID_MAX_ROWS,
            ),
            winner_row_ok=_require_bool(obj.get("winner_row_ok"), name="row.winner_row_ok"),
            dominated_by_winner_ok=_require_bool(
                obj.get("dominated_by_winner_ok"),
                name="row.dominated_by_winner_ok",
            ),
            schema=schema,
        )


@dataclass(frozen=True)
class UniformBatchPriceGridWitnessV1:
    settlement_id: str
    uniform_batch_certificate_hash: str
    candidate_table_root: str
    winner_candidate_id: str
    winner_price_num: int
    winner_price_den: int
    volume_upper: int
    surplus_upper_at_winner_volume: int
    table_complete_ok: bool
    certificate_bound_ok: bool
    global_grid_optimality_ok: bool
    schema: str = UPBA_PRICE_GRID_WITNESS_SCHEMA_V1

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema": self.schema,
            "settlement_id": self.settlement_id,
            "uniform_batch_certificate_hash": self.uniform_batch_certificate_hash,
            "candidate_table_root": self.candidate_table_root,
            "winner_candidate_id": self.winner_candidate_id,
            "winner_price_num": int(self.winner_price_num),
            "winner_price_den": int(self.winner_price_den),
            "volume_upper": int(self.volume_upper),
            "surplus_upper_at_winner_volume": int(self.surplus_upper_at_winner_volume),
            "table_complete_ok": bool(self.table_complete_ok),
            "certificate_bound_ok": bool(self.certificate_bound_ok),
            "global_grid_optimality_ok": bool(self.global_grid_optimality_ok),
        }

    @classmethod
    def from_obj(cls, obj: Mapping[str, Any]) -> "UniformBatchPriceGridWitnessV1":
        _reject_unknown_keys(obj, allowed=_WITNESS_KEYS, name="price_grid.witness")
        schema = _require_str(obj.get("schema"), name="witness.schema")
        if schema != UPBA_PRICE_GRID_WITNESS_SCHEMA_V1:
            raise ValueError("unsupported price grid witness schema")
        return cls(
            settlement_id=_require_str(obj.get("settlement_id"), name="witness.settlement_id"),
            uniform_batch_certificate_hash=_require_sha256_hex(
                obj.get("uniform_batch_certificate_hash"),
                name="witness.uniform_batch_certificate_hash",
            ),
            candidate_table_root=_require_sha256_hex(
                obj.get("candidate_table_root"),
                name="witness.candidate_table_root",
            ),
            winner_candidate_id=_require_sha256_hex(obj.get("winner_candidate_id"), name="witness.winner_candidate_id"),
            winner_price_num=_require_nonnegative_int(obj.get("winner_price_num"), name="witness.winner_price_num"),
            winner_price_den=_require_nonnegative_int(obj.get("winner_price_den"), name="witness.winner_price_den"),
            volume_upper=_require_nonnegative_int(
                obj.get("volume_upper"),
                name="witness.volume_upper",
                maximum=UNIFORM_BATCH_OUTPUT_AMOUNT_MAX * UPBA_PRICE_GRID_MAX_ROWS,
            ),
            surplus_upper_at_winner_volume=_require_nonnegative_int(
                obj.get("surplus_upper_at_winner_volume"),
                name="witness.surplus_upper_at_winner_volume",
                maximum=UNIFORM_BATCH_OUTPUT_AMOUNT_MAX * DEX_SWAP_AMOUNT_MAX * UPBA_PRICE_GRID_MAX_ROWS,
            ),
            table_complete_ok=_require_bool(obj.get("table_complete_ok"), name="witness.table_complete_ok"),
            certificate_bound_ok=_require_bool(
                obj.get("certificate_bound_ok"),
                name="witness.certificate_bound_ok",
            ),
            global_grid_optimality_ok=_require_bool(
                obj.get("global_grid_optimality_ok"),
                name="witness.global_grid_optimality_ok",
            ),
            schema=schema,
        )


@dataclass(frozen=True)
class UniformBatchPriceGridTauFactsV1:
    has_upba_certificate: bool
    has_candidate_table: bool
    has_optimality_witness: bool
    policy_id_ok: bool
    table_root_matches_certificate: bool
    row_count_ok: bool
    grid_complete_ok: bool
    scores_recomputed_ok: bool
    winner_binding_ok: bool
    winner_feasible_ok: bool
    dominance_ok: bool
    certificate_bound_ok: bool
    no_unknown_rows_ok: bool
    all_required_roots_bound_ok: bool
    global_grid_optimality_ok: bool

    def to_dict(self) -> dict[str, bool]:
        return {
            "has_upba_certificate": self.has_upba_certificate,
            "has_candidate_table": self.has_candidate_table,
            "has_optimality_witness": self.has_optimality_witness,
            "policy_id_ok": self.policy_id_ok,
            "table_root_matches_certificate": self.table_root_matches_certificate,
            "row_count_ok": self.row_count_ok,
            "grid_complete_ok": self.grid_complete_ok,
            "scores_recomputed_ok": self.scores_recomputed_ok,
            "winner_binding_ok": self.winner_binding_ok,
            "winner_feasible_ok": self.winner_feasible_ok,
            "dominance_ok": self.dominance_ok,
            "certificate_bound_ok": self.certificate_bound_ok,
            "no_unknown_rows_ok": self.no_unknown_rows_ok,
            "all_required_roots_bound_ok": self.all_required_roots_bound_ok,
            "global_grid_optimality_ok": self.global_grid_optimality_ok,
        }


@dataclass(frozen=True)
class UniformBatchPriceGridVerificationResult:
    ok: bool
    error: str | None
    candidate_table_root: str | None = None
    winner_candidate_id: str | None = None
    tau_facts: dict[str, bool] | None = None


def verify_uniform_batch_price_grid_table_v1(
    *,
    intents: Sequence[Intent],
    pool: PoolState,
    balances: BalanceTable,
    uniform_batch_certificate: UniformBatchCertificateV1 | Mapping[str, Any],
    config: UniformBatchPriceGridConfigV1 | Mapping[str, Any],
    rows: Sequence[UniformBatchPriceGridRowV1 | Mapping[str, Any]],
    witness: UniformBatchPriceGridWitnessV1 | Mapping[str, Any],
) -> UniformBatchPriceGridVerificationResult:
    try:
        cert = (
            uniform_batch_certificate
            if isinstance(uniform_batch_certificate, UniformBatchCertificateV1)
            else UniformBatchCertificateV1.from_obj(
                _require_mapping(uniform_batch_certificate, name="uniform_batch_certificate")
            )
        )
        parsed_config = (
            config
            if isinstance(config, UniformBatchPriceGridConfigV1)
            else UniformBatchPriceGridConfigV1.from_obj(
                _require_mapping(config, name="price_grid.config")
            )
        )
        parsed_rows = tuple(
            row if isinstance(row, UniformBatchPriceGridRowV1) else UniformBatchPriceGridRowV1.from_obj(
                _require_mapping(row, name="price_grid.row")
            )
            for row in rows
        )
        parsed_witness = (
            witness
            if isinstance(witness, UniformBatchPriceGridWitnessV1)
            else UniformBatchPriceGridWitnessV1.from_obj(_require_mapping(witness, name="price_grid.witness"))
        )
        _verify_price_grid_table(
            intents=tuple(intents),
            pool=pool,
            balances=balances,
            certificate=cert,
            config=parsed_config,
            rows=parsed_rows,
            witness=parsed_witness,
        )
        facts = UniformBatchPriceGridTauFactsV1(
            has_upba_certificate=True,
            has_candidate_table=True,
            has_optimality_witness=True,
            policy_id_ok=True,
            table_root_matches_certificate=True,
            row_count_ok=True,
            grid_complete_ok=True,
            scores_recomputed_ok=True,
            winner_binding_ok=True,
            winner_feasible_ok=True,
            dominance_ok=True,
            certificate_bound_ok=True,
            no_unknown_rows_ok=True,
            all_required_roots_bound_ok=True,
            global_grid_optimality_ok=True,
        )
        return UniformBatchPriceGridVerificationResult(
            ok=True,
            error=None,
            candidate_table_root=parsed_config.candidate_table_root,
            winner_candidate_id=parsed_witness.winner_candidate_id,
            tau_facts=facts.to_dict(),
        )
    except (TypeError, ValueError) as exc:
        return UniformBatchPriceGridVerificationResult(ok=False, error=str(exc))


def build_uniform_batch_price_grid_table_v1(
    *,
    intents: Sequence[Intent],
    pool: PoolState,
    balances: BalanceTable,
    uniform_batch_certificate: UniformBatchCertificateV1 | Mapping[str, Any],
    settlement_id: str,
    max_price_num: int,
    max_price_den: int,
) -> tuple[
    UniformBatchPriceGridConfigV1,
    tuple[UniformBatchPriceGridRowV1, ...],
    UniformBatchPriceGridWitnessV1,
]:
    cert = (
        uniform_batch_certificate
        if isinstance(uniform_batch_certificate, UniformBatchCertificateV1)
        else UniformBatchCertificateV1.from_obj(
            _require_mapping(uniform_batch_certificate, name="uniform_batch_certificate")
        )
    )
    _validate_table_scope(
        intents=tuple(intents),
        pool=pool,
        certificate=cert,
        settlement_id=settlement_id,
        max_price_num=max_price_num,
        max_price_den=max_price_den,
    )
    _verify_uniform_batch_certificate_or_raise(
        intents=tuple(intents),
        pool=pool,
        balances=balances,
        certificate=cert,
    )
    certificate_hash = uniform_batch_certificate_hash(cert)
    rows_without_dominance: list[UniformBatchPriceGridRowV1] = []
    score_by_key: dict[tuple[int, int], UniformBatchPriceGridScoreV1] = {}
    for price_num in range(max_price_num + 1):
        for price_den in range(max_price_den + 1):
            score = _score_price(
                intents=tuple(intents),
                pool=pool,
                balances=balances,
                price_num=price_num,
                price_den=price_den,
            )
            score_by_key[(price_num, price_den)] = score
            is_winner = (price_num, price_den) == (cert.price_num, cert.price_den)
            candidate_id = uniform_batch_price_grid_candidate_id(
                settlement_id=settlement_id,
                score_function_id=UPBA_PRICE_GRID_SCORE_FUNCTION_ID_V1,
                price_num=price_num,
                price_den=price_den,
                valid_price_ok=score.valid_price_ok,
                volume=score.volume,
                surplus=score.surplus,
            )
            rows_without_dominance.append(
                UniformBatchPriceGridRowV1(
                    settlement_id=settlement_id,
                    price_num=price_num,
                    price_den=price_den,
                    candidate_id=candidate_id,
                    valid_price_ok=score.valid_price_ok,
                    score_recomputed_ok=True,
                    volume=score.volume,
                    surplus=score.surplus,
                    winner_row_ok=is_winner,
                    dominated_by_winner_ok=False,
                )
            )
    winner_score = score_by_key.get((cert.price_num, cert.price_den))
    if winner_score is None:
        raise ValueError("uniform batch certificate price is outside configured grid")
    rows: list[UniformBatchPriceGridRowV1] = []
    for row in rows_without_dominance:
        dominated = _score_dominates(
            winner_score,
            UniformBatchPriceGridScoreV1(row.valid_price_ok, row.volume, row.surplus),
        )
        rows.append(
            UniformBatchPriceGridRowV1(
                settlement_id=row.settlement_id,
                price_num=row.price_num,
                price_den=row.price_den,
                candidate_id=row.candidate_id,
                valid_price_ok=row.valid_price_ok,
                score_recomputed_ok=row.score_recomputed_ok,
                volume=row.volume,
                surplus=row.surplus,
                winner_row_ok=row.winner_row_ok,
                dominated_by_winner_ok=dominated,
            )
        )
    rows_tuple = tuple(sorted(rows, key=lambda item: (item.price_num, item.price_den)))
    table_root = uniform_batch_price_grid_table_root(
        settlement_id=settlement_id,
        max_price_num=max_price_num,
        max_price_den=max_price_den,
        score_function_id=UPBA_PRICE_GRID_SCORE_FUNCTION_ID_V1,
        rows=rows_tuple,
    )
    winner_row = _single_winner_row(rows_tuple)
    config = UniformBatchPriceGridConfigV1(
        settlement_id=settlement_id,
        pool_id=pool.pool_id,
        policy_id=UNIFORM_BATCH_POLICY_V1_ID,
        max_price_num=max_price_num,
        max_price_den=max_price_den,
        score_function_id=UPBA_PRICE_GRID_SCORE_FUNCTION_ID_V1,
        candidate_table_root=table_root,
        row_count=len(rows_tuple),
    )
    witness = UniformBatchPriceGridWitnessV1(
        settlement_id=settlement_id,
        uniform_batch_certificate_hash=certificate_hash,
        candidate_table_root=table_root,
        winner_candidate_id=winner_row.candidate_id,
        winner_price_num=winner_row.price_num,
        winner_price_den=winner_row.price_den,
        volume_upper=winner_row.volume,
        surplus_upper_at_winner_volume=winner_row.surplus,
        table_complete_ok=True,
        certificate_bound_ok=True,
        global_grid_optimality_ok=True,
    )
    _verify_price_grid_table(
        intents=tuple(intents),
        pool=pool,
        balances=balances,
        certificate=cert,
        config=config,
        rows=rows_tuple,
        witness=witness,
    )
    return config, rows_tuple, witness


def uniform_batch_price_grid_candidate_id(
    *,
    settlement_id: str,
    score_function_id: str,
    price_num: int,
    price_den: int,
    valid_price_ok: bool,
    volume: int,
    surplus: int,
) -> str:
    settlement_id = _require_str(settlement_id, name="candidate.settlement_id")
    score_function_id = _require_str(score_function_id, name="candidate.score_function_id")
    price_num = _require_nonnegative_int(price_num, name="candidate.price_num")
    price_den = _require_nonnegative_int(price_den, name="candidate.price_den")
    valid_price_ok = _require_bool(valid_price_ok, name="candidate.valid_price_ok")
    volume = _require_nonnegative_int(
        volume,
        name="candidate.volume",
        maximum=UNIFORM_BATCH_OUTPUT_AMOUNT_MAX * UPBA_PRICE_GRID_MAX_ROWS,
    )
    surplus = _require_nonnegative_int(
        surplus,
        name="candidate.surplus",
        maximum=UNIFORM_BATCH_OUTPUT_AMOUNT_MAX * DEX_SWAP_AMOUNT_MAX * UPBA_PRICE_GRID_MAX_ROWS,
    )
    body = {
        "schema": UPBA_PRICE_GRID_CANDIDATE_ID_SCHEMA_V1,
        "settlement_id": settlement_id,
        "score_function_id": score_function_id,
        "price_num": int(price_num),
        "price_den": int(price_den),
        "valid_price_ok": bool(valid_price_ok),
        "volume": int(volume),
        "surplus": int(surplus),
    }
    return sha256_hex(
        domain_sep_bytes("upba_price_grid_candidate_id", version=1)
        + canonical_json_bytes(body)
    )


def uniform_batch_price_grid_table_root(
    *,
    settlement_id: str,
    max_price_num: int,
    max_price_den: int,
    score_function_id: str,
    rows: Sequence[UniformBatchPriceGridRowV1 | Mapping[str, Any]],
) -> str:
    settlement_id = _require_str(settlement_id, name="table_root.settlement_id")
    max_price_num = _require_nonnegative_int(max_price_num, name="table_root.max_price_num")
    max_price_den = _require_nonnegative_int(max_price_den, name="table_root.max_price_den")
    _expected_row_count(max_price_num, max_price_den)
    score_function_id = _require_str(score_function_id, name="table_root.score_function_id")
    if score_function_id != UPBA_PRICE_GRID_SCORE_FUNCTION_ID_V1:
        raise ValueError("unsupported price grid score_function_id")
    parsed_rows = tuple(
        row if isinstance(row, UniformBatchPriceGridRowV1) else UniformBatchPriceGridRowV1.from_obj(
            _require_mapping(row, name="price_grid.row")
        )
        for row in rows
    )
    for row in parsed_rows:
        _validate_row_values(row)
    body = {
        "schema": UPBA_PRICE_GRID_TABLE_ROOT_SCHEMA_V1,
        "settlement_id": settlement_id,
        "max_price_num": int(max_price_num),
        "max_price_den": int(max_price_den),
        "score_function_id": score_function_id,
        "rows": [
            row.to_dict()
            for row in sorted(parsed_rows, key=lambda item: (item.price_num, item.price_den))
        ],
    }
    return sha256_hex(
        domain_sep_bytes("upba_price_grid_table", version=1)
        + canonical_json_bytes(body)
    )


def _verify_price_grid_table(
    *,
    intents: tuple[Intent, ...],
    pool: PoolState,
    balances: BalanceTable,
    certificate: UniformBatchCertificateV1,
    config: UniformBatchPriceGridConfigV1,
    rows: tuple[UniformBatchPriceGridRowV1, ...],
    witness: UniformBatchPriceGridWitnessV1,
) -> None:
    _validate_config_values(config)
    for row in rows:
        _validate_row_values(row)
    _validate_witness_values(witness)
    _validate_table_scope(
        intents=intents,
        pool=pool,
        certificate=certificate,
        settlement_id=config.settlement_id,
        max_price_num=config.max_price_num,
        max_price_den=config.max_price_den,
    )
    _verify_uniform_batch_certificate_or_raise(
        intents=intents,
        pool=pool,
        balances=balances,
        certificate=certificate,
    )
    if config.pool_id != pool.pool_id:
        raise ValueError("price grid config pool_id mismatch")
    if config.policy_id != certificate.policy_id:
        raise ValueError("price grid config policy_id mismatch")
    if witness.settlement_id != config.settlement_id:
        raise ValueError("price grid witness settlement_id mismatch")
    if witness.uniform_batch_certificate_hash != uniform_batch_certificate_hash(certificate):
        raise ValueError("price grid witness uniform_batch_certificate_hash mismatch")
    if witness.candidate_table_root != config.candidate_table_root:
        raise ValueError("price grid witness candidate_table_root mismatch")
    for flag_name in ("table_complete_ok", "certificate_bound_ok", "global_grid_optimality_ok"):
        if not getattr(witness, flag_name):
            raise ValueError(f"price grid witness {flag_name} must be true")
    expected_row_count = _expected_row_count(config.max_price_num, config.max_price_den)
    if config.row_count != expected_row_count:
        raise ValueError("price grid config row_count mismatch")
    if len(rows) != expected_row_count:
        raise ValueError("price grid row count mismatch")
    actual_root = uniform_batch_price_grid_table_root(
        settlement_id=config.settlement_id,
        max_price_num=config.max_price_num,
        max_price_den=config.max_price_den,
        score_function_id=config.score_function_id,
        rows=rows,
    )
    if config.candidate_table_root != actual_root:
        raise ValueError("price grid candidate_table_root mismatch")

    seen_keys: set[tuple[int, int]] = set()
    rows_by_key: dict[tuple[int, int], UniformBatchPriceGridRowV1] = {}
    for row in rows:
        if row.settlement_id != config.settlement_id:
            raise ValueError("price grid row settlement_id mismatch")
        key = (row.price_num, row.price_den)
        if key in seen_keys:
            raise ValueError("duplicate price grid row key")
        seen_keys.add(key)
        if row.price_num > config.max_price_num or row.price_den > config.max_price_den:
            raise ValueError("price grid row key outside configured bounds")
        expected_score = _score_price(
            intents=intents,
            pool=pool,
            balances=balances,
            price_num=row.price_num,
            price_den=row.price_den,
        )
        if not row.score_recomputed_ok:
            raise ValueError("price grid row score_recomputed_ok must be true")
        if row.valid_price_ok != expected_score.valid_price_ok:
            raise ValueError("price grid row valid_price_ok mismatch")
        if row.volume != expected_score.volume:
            raise ValueError("price grid row volume mismatch")
        if row.surplus != expected_score.surplus:
            raise ValueError("price grid row surplus mismatch")
        expected_candidate_id = uniform_batch_price_grid_candidate_id(
            settlement_id=config.settlement_id,
            score_function_id=config.score_function_id,
            price_num=row.price_num,
            price_den=row.price_den,
            valid_price_ok=row.valid_price_ok,
            volume=row.volume,
            surplus=row.surplus,
        )
        if row.candidate_id != expected_candidate_id:
            raise ValueError("price grid row candidate_id mismatch")
        rows_by_key[key] = row
    for price_num in range(config.max_price_num + 1):
        for price_den in range(config.max_price_den + 1):
            if (price_num, price_den) not in rows_by_key:
                raise ValueError("price grid missing bounded row")
    winner_row = _single_winner_row(rows)
    if (winner_row.price_num, winner_row.price_den) != (witness.winner_price_num, witness.winner_price_den):
        raise ValueError("price grid witness winner price mismatch")
    if witness.winner_candidate_id != winner_row.candidate_id:
        raise ValueError("price grid witness winner_candidate_id mismatch")
    if (winner_row.price_num, winner_row.price_den) != (certificate.price_num, certificate.price_den):
        raise ValueError("price grid winner price does not match uniform batch certificate price")
    if not winner_row.valid_price_ok:
        raise ValueError("price grid winner row must be valid")
    if witness.volume_upper != winner_row.volume:
        raise ValueError("price grid witness volume_upper mismatch")
    if witness.surplus_upper_at_winner_volume != winner_row.surplus:
        raise ValueError("price grid witness surplus upper bound mismatch")
    winner_score = UniformBatchPriceGridScoreV1(
        valid_price_ok=winner_row.valid_price_ok,
        volume=winner_row.volume,
        surplus=winner_row.surplus,
    )
    for row in rows:
        row_score = UniformBatchPriceGridScoreV1(row.valid_price_ok, row.volume, row.surplus)
        dominated = _score_dominates(winner_score, row_score)
        if row.dominated_by_winner_ok != dominated:
            raise ValueError("price grid row dominated_by_winner_ok mismatch")
        if not dominated:
            raise ValueError("price grid winner does not dominate candidate row")


def _validate_table_scope(
    *,
    intents: tuple[Intent, ...],
    pool: PoolState,
    certificate: UniformBatchCertificateV1,
    settlement_id: str,
    max_price_num: int,
    max_price_den: int,
) -> None:
    _require_str(settlement_id, name="settlement_id")
    if certificate.schema != UNIFORM_BATCH_CERTIFICATE_SCHEMA_V1:
        raise ValueError("price grid verifier supports UPBA v1 certificate schema only")
    if certificate.policy_id != UNIFORM_BATCH_POLICY_V1_ID:
        raise ValueError("price grid verifier supports UPBA v1 full-fill policy only")
    if certificate.pool_id != pool.pool_id:
        raise ValueError("price grid certificate pool_id mismatch")
    if certificate.pool_state_hash != uniform_batch_pool_state_hash(pool):
        raise ValueError("price grid certificate pool_state_hash mismatch")
    if certificate.intent_set_hash != uniform_batch_intent_set_hash(intents):
        raise ValueError("price grid certificate intent_set_hash mismatch")
    if pool.status != PoolStatus.ACTIVE:
        raise ValueError("price grid pool must be active")
    if pool.curve_tag != CURVE_TAG_CPMM:
        raise ValueError("price grid verifier supports CPMM pools only")
    if pool.reserve0 <= 0 or pool.reserve1 <= 0:
        raise ValueError("price grid pool reserves must be positive")
    _require_nonnegative_int(max_price_num, name="max_price_num")
    _require_nonnegative_int(max_price_den, name="max_price_den")
    _expected_row_count(max_price_num, max_price_den)
    if certificate.price_num > max_price_num or certificate.price_den > max_price_den:
        raise ValueError("uniform batch certificate price outside configured grid")
    for intent in intents:
        _validate_intent_scope(intent=intent, pool=pool, certificate=certificate)


def _verify_uniform_batch_certificate_or_raise(
    *,
    intents: tuple[Intent, ...],
    pool: PoolState,
    balances: BalanceTable,
    certificate: UniformBatchCertificateV1,
) -> None:
    result = verify_uniform_batch_certificate_v1(
        intents=intents,
        pool=pool,
        balances=balances,
        certificate=certificate,
    )
    if not result.ok:
        raise ValueError(f"price grid uniform batch certificate invalid: {result.error}")


def _validate_config_values(config: UniformBatchPriceGridConfigV1) -> None:
    if config.schema != UPBA_PRICE_GRID_CONFIG_SCHEMA_V1:
        raise ValueError("unsupported price grid config schema")
    _require_str(config.settlement_id, name="config.settlement_id")
    _require_str(config.pool_id, name="config.pool_id")
    if config.policy_id != UNIFORM_BATCH_POLICY_V1_ID:
        raise ValueError("price grid verifier supports UPBA v1 full-fill policy only")
    _require_nonnegative_int(config.max_price_num, name="config.max_price_num")
    _require_nonnegative_int(config.max_price_den, name="config.max_price_den")
    if config.score_function_id != UPBA_PRICE_GRID_SCORE_FUNCTION_ID_V1:
        raise ValueError("unsupported price grid score_function_id")
    _require_sha256_hex(config.candidate_table_root, name="config.candidate_table_root")
    _require_nonnegative_int(config.row_count, name="config.row_count")


def _validate_row_values(row: UniformBatchPriceGridRowV1) -> None:
    if row.schema != UPBA_PRICE_GRID_ROW_SCHEMA_V1:
        raise ValueError("unsupported price grid row schema")
    _require_str(row.settlement_id, name="row.settlement_id")
    _require_nonnegative_int(row.price_num, name="row.price_num")
    _require_nonnegative_int(row.price_den, name="row.price_den")
    _require_sha256_hex(row.candidate_id, name="row.candidate_id")
    _require_bool(row.valid_price_ok, name="row.valid_price_ok")
    _require_bool(row.score_recomputed_ok, name="row.score_recomputed_ok")
    _require_nonnegative_int(
        row.volume,
        name="row.volume",
        maximum=UNIFORM_BATCH_OUTPUT_AMOUNT_MAX * UPBA_PRICE_GRID_MAX_ROWS,
    )
    _require_nonnegative_int(
        row.surplus,
        name="row.surplus",
        maximum=UNIFORM_BATCH_OUTPUT_AMOUNT_MAX * DEX_SWAP_AMOUNT_MAX * UPBA_PRICE_GRID_MAX_ROWS,
    )
    _require_bool(row.winner_row_ok, name="row.winner_row_ok")
    _require_bool(row.dominated_by_winner_ok, name="row.dominated_by_winner_ok")


def _validate_witness_values(witness: UniformBatchPriceGridWitnessV1) -> None:
    if witness.schema != UPBA_PRICE_GRID_WITNESS_SCHEMA_V1:
        raise ValueError("unsupported price grid witness schema")
    _require_str(witness.settlement_id, name="witness.settlement_id")
    _require_sha256_hex(
        witness.uniform_batch_certificate_hash,
        name="witness.uniform_batch_certificate_hash",
    )
    _require_sha256_hex(witness.candidate_table_root, name="witness.candidate_table_root")
    _require_sha256_hex(witness.winner_candidate_id, name="witness.winner_candidate_id")
    _require_nonnegative_int(witness.winner_price_num, name="witness.winner_price_num")
    _require_nonnegative_int(witness.winner_price_den, name="witness.winner_price_den")
    _require_nonnegative_int(
        witness.volume_upper,
        name="witness.volume_upper",
        maximum=UNIFORM_BATCH_OUTPUT_AMOUNT_MAX * UPBA_PRICE_GRID_MAX_ROWS,
    )
    _require_nonnegative_int(
        witness.surplus_upper_at_winner_volume,
        name="witness.surplus_upper_at_winner_volume",
        maximum=UNIFORM_BATCH_OUTPUT_AMOUNT_MAX * DEX_SWAP_AMOUNT_MAX * UPBA_PRICE_GRID_MAX_ROWS,
    )
    _require_bool(witness.table_complete_ok, name="witness.table_complete_ok")
    _require_bool(witness.certificate_bound_ok, name="witness.certificate_bound_ok")
    _require_bool(witness.global_grid_optimality_ok, name="witness.global_grid_optimality_ok")


def _score_price(
    *,
    intents: tuple[Intent, ...],
    pool: PoolState,
    balances: BalanceTable,
    price_num: int,
    price_den: int,
) -> UniformBatchPriceGridScoreV1:
    if price_num <= 0 or price_den <= 0:
        return UniformBatchPriceGridScoreV1(valid_price_ok=False, volume=0, surplus=0)
    if price_num > DEX_POOL_RESERVE_MAX or price_den > DEX_POOL_RESERVE_MAX:
        return UniformBatchPriceGridScoreV1(valid_price_ok=False, volume=0, surplus=0)
    balance_net: dict[tuple[str, str], int] = defaultdict(int)
    reserve_net: dict[str, int] = defaultdict(int)
    volume = 0
    surplus = 0
    for intent in sorted(intents, key=lambda item: item.intent_id):
        direction = _intent_direction(intent=intent, pool=pool)
        asset_in = str(intent.get_field("asset_in"))
        asset_out = str(intent.get_field("asset_out"))
        sender = str(intent.sender_pubkey)
        recipient = str(intent.get_field("recipient", sender))
        amount_in = _require_positive_int(
            intent.get_field("amount_in"),
            name="intent.amount_in",
            maximum=DEX_SWAP_AMOUNT_MAX,
        )
        min_amount_out = _require_nonnegative_int(
            intent.get_field("min_amount_out"),
            name="intent.min_amount_out",
            maximum=UNIFORM_BATCH_OUTPUT_AMOUNT_MAX,
        )
        fee_paid = compute_fee_total(amount_in, pool.fee_bps)
        net_in = amount_in - fee_paid
        if net_in <= 0:
            continue
        amount_out = _uniform_price_out(
            net_in=net_in,
            direction=direction,
            price_num=price_num,
            price_den=price_den,
        )
        if amount_out * amount_in < min_amount_out * amount_in:
            continue
        if balances.get(sender, asset_in) + balance_net[(sender, asset_in)] < amount_in:
            continue
        balance_net[(sender, asset_in)] -= amount_in
        balance_net[(recipient, asset_out)] += amount_out
        reserve_net[asset_in] += amount_in
        reserve_net[asset_out] -= amount_out
        volume += amount_in
        surplus += amount_out * amount_in - min_amount_out * amount_in
    reserve0_after = pool.reserve0 + reserve_net[pool.asset0]
    reserve1_after = pool.reserve1 + reserve_net[pool.asset1]
    if reserve0_after < 0 or reserve1_after < 0:
        return UniformBatchPriceGridScoreV1(valid_price_ok=False, volume=0, surplus=0)
    if reserve0_after > DEX_POOL_RESERVE_MAX or reserve1_after > DEX_POOL_RESERVE_MAX:
        return UniformBatchPriceGridScoreV1(valid_price_ok=False, volume=0, surplus=0)
    if reserve0_after * reserve1_after < pool.reserve0 * pool.reserve1:
        return UniformBatchPriceGridScoreV1(valid_price_ok=False, volume=0, surplus=0)
    return UniformBatchPriceGridScoreV1(valid_price_ok=True, volume=volume, surplus=surplus)


def _score_dominates(winner: UniformBatchPriceGridScoreV1, other: UniformBatchPriceGridScoreV1) -> bool:
    if other.volume > winner.volume:
        return False
    if other.volume == winner.volume and other.surplus > winner.surplus:
        return False
    return True


def _single_winner_row(rows: Sequence[UniformBatchPriceGridRowV1]) -> UniformBatchPriceGridRowV1:
    winners = [row for row in rows if row.winner_row_ok]
    if len(winners) != 1:
        raise ValueError("price grid requires exactly one winner row")
    return winners[0]


def _expected_row_count(max_price_num: int, max_price_den: int) -> int:
    max_price_num = _require_nonnegative_int(max_price_num, name="max_price_num")
    max_price_den = _require_nonnegative_int(max_price_den, name="max_price_den")
    row_count = (max_price_num + 1) * (max_price_den + 1)
    if row_count > UPBA_PRICE_GRID_MAX_ROWS:
        raise ValueError(f"price grid row count exceeds maximum {UPBA_PRICE_GRID_MAX_ROWS}")
    return row_count


def _validate_intent_scope(*, intent: Intent, pool: PoolState, certificate: UniformBatchCertificateV1) -> None:
    if intent.kind != IntentKind.SWAP_EXACT_IN:
        raise ValueError("price grid verifier supports SWAP_EXACT_IN only")
    if str(intent.get_field("pool_id")) != pool.pool_id:
        raise ValueError("price grid intent pool_id mismatch")
    asset_in = str(intent.get_field("asset_in"))
    asset_out = str(intent.get_field("asset_out"))
    if {asset_in, asset_out} != {certificate.base_asset, certificate.quote_asset}:
        raise ValueError("price grid intent asset pair mismatch")
    if asset_in == asset_out:
        raise ValueError("price grid intent assets must differ")
    _require_str(intent.sender_pubkey, name="intent.sender_pubkey")
    _require_str(intent.get_field("recipient", intent.sender_pubkey), name="intent.recipient")
    _require_positive_int(intent.get_field("amount_in"), name="intent.amount_in", maximum=DEX_SWAP_AMOUNT_MAX)
    _require_nonnegative_int(
        intent.get_field("min_amount_out"),
        name="intent.min_amount_out",
        maximum=UNIFORM_BATCH_OUTPUT_AMOUNT_MAX,
    )


def _intent_direction(*, intent: Intent, pool: PoolState) -> str:
    asset_in = str(intent.get_field("asset_in"))
    asset_out = str(intent.get_field("asset_out"))
    if asset_in == pool.asset0 and asset_out == pool.asset1:
        return "base_to_quote"
    if asset_in == pool.asset1 and asset_out == pool.asset0:
        return "quote_to_base"
    raise ValueError("price grid intent direction mismatch")


def _uniform_price_out(*, net_in: int, direction: str, price_num: int, price_den: int) -> int:
    if direction == "base_to_quote":
        return (net_in * price_num) // price_den
    if direction == "quote_to_base":
        return (net_in * price_den) // price_num
    raise ValueError("unsupported price grid direction")


def _require_mapping(value: Any, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be an object")
    return value


def _reject_unknown_keys(value: Mapping[str, Any], *, allowed: frozenset[str], name: str) -> None:
    unknown = sorted(set(value) - set(allowed))
    if unknown:
        joined = ", ".join(unknown)
        raise ValueError(f"{name} contains unsupported keys: {joined}")


def _require_str(value: Any, *, name: str) -> str:
    if not isinstance(value, str) or not value:
        raise TypeError(f"{name} must be a non-empty string")
    return str(value)


def _require_bool(value: Any, *, name: str) -> bool:
    if not isinstance(value, bool):
        raise TypeError(f"{name} must be a bool")
    return bool(value)


def _require_sha256_hex(value: Any, *, name: str) -> str:
    parsed = _require_str(value, name=name)
    if (
        len(parsed) != 66
        or not parsed.startswith("0x")
        or any(char not in "0123456789abcdef" for char in parsed[2:])
    ):
        raise ValueError(f"{name} must be 0x-prefixed lowercase sha256 hex")
    return parsed


def _require_nonnegative_int(value: Any, *, name: str, maximum: int | None = None) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    if value < 0:
        raise ValueError(f"{name} must be non-negative")
    if maximum is not None and value > maximum:
        raise ValueError(f"{name} exceeds maximum")
    return int(value)


def _require_positive_int(value: Any, *, name: str, maximum: int | None = None) -> int:
    value_int = _require_nonnegative_int(value, name=name, maximum=maximum)
    if value_int <= 0:
        raise ValueError(f"{name} must be positive")
    return value_int
