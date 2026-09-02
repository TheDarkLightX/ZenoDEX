#!/usr/bin/env python3
"""Independent oracle for the bounded `ASSET_TRANSFER` refinement corpus.

This module never imports or calls either runtime transition. It recomputes every
expected observation in ``tests/data/asset_transfer_refinement_v1.json`` from the
recorded context/pre-state/command under ``REJECT_PRECEDENCE_V1``, with every role
delta aggregated before the signed 128-bit width check and with debit
insufficiency ranked above credit overflow independently of principal spelling.

Authority: bounded executable research evidence only. Nothing here creates
production, settlement, release, migration, proof, or value-moving authority, and
``custody_domain`` is an accounting-location/control-domain label rather than a
claim of possession or legal title.
"""

from __future__ import annotations

import argparse
import json
import re
from collections.abc import Callable, Mapping
from dataclasses import dataclass
from pathlib import Path
from types import MappingProxyType
from typing import Any, Final, NoReturn

CORPUS_SCHEMA_V1: Final = "zenodex/asset-transfer-refinement-corpus/v1"
CHECK_SCHEMA_V1: Final = "zenodex/asset-transfer-refinement-check/v1"
REPO_ROOT: Final = Path(__file__).resolve().parents[1]
CORPUS_PATH: Final = REPO_ROOT / "tests" / "data" / "asset_transfer_refinement_v1.json"

COMMAND_KIND_V1: Final = "asset_transfer"
CUSTODY_DOMAIN_V1: Final = "accounts"
ACCOUNT_MOVEMENT_V1: Final = "ACCOUNT_MOVEMENT"
FEE_ALLOCATION_V1: Final = "FEE_ALLOCATION"
DEFECT_KILLED_V1: Final = "killed_by_this_corpus"

MAX_ATOMS_V1: Final = (1 << 128) - 1
MIN_DELTA_ATOMS_V1: Final = -(1 << 127)
MAX_DELTA_ATOMS_V1: Final = (1 << 127) - 1
MAX_WRITER_EPOCH_V1: Final = (1 << 64) - 1
MAX_TOKEN_BYTES_V1: Final = 160

REJECT_PRECEDENCE_V1: Final = (
    "RELEASE_MISMATCH", "UNKNOWN_COMMAND", "UNKNOWN_ASSET", "DISABLED_ASSET",
    "UNAUTHORIZED_SUBJECT", "SELF_TRANSFER", "ZERO_AMOUNT", "FEE_LIMIT_EXCEEDED",
    "EFFECT_DELTA_OVERFLOW", "INSUFFICIENT_BALANCE", "BALANCE_OVERFLOW",
    "POST_STATE_RESOURCE_BOUND_EXCEEDED",
)
# `UNKNOWN_ASSET` and `DISABLED_ASSET` cannot be violated by one command at once,
# so their pairwise witness carries a disabled-policy lure instead.
MUTUALLY_EXCLUSIVE_PAIRS_V1: Final = (("UNKNOWN_ASSET", "DISABLED_ASSET"),)
FEE_OWNER_ROLES_V1: Final = ("distinct", "none", "recipient", "sender")
ACCEPTED_FEE_OWNER_ROLES_V1: Final = ("distinct", "recipient", "sender")
REQUIRED_OBSERVATIONS_V1: Final = (
    "accepted_asset_conservation", "accepted_effect_rows", "accepted_empty_external_outbox",
    "accepted_fee_conservation", "accepted_lane_write_pre_post_binding",
    "accepted_occurrence_consumptions", "accepted_post_balances", "deterministic_repeated_replay",
    "rejection_code", "rejection_empty_effect_plan", "rejection_pre_post_root_equality",
)

_TOKEN_RE: Final = re.compile(r"\A[\x21-\x7e]+\Z")
_ATOMS_RE: Final = re.compile(r"\A(?:0|[1-9][0-9]*)\Z")
_ROOT_RE: Final = re.compile(r"\A0x[0-9a-f]{64}\Z")

Parser = Callable[[Any, str], Any]


class RefinementCorpusErrorV1(ValueError):
    """Raised when the refinement corpus is not exactly well formed."""


def _fail(message: str) -> NoReturn:
    raise RefinementCorpusErrorV1(message)


def _reject_duplicate_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            _fail(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def _text(value: Any, where: str) -> str:
    if type(value) is not str:
        _fail(f"{where} must be a JSON string")
    if not value:
        _fail(f"{where} must not be empty")
    return value


def _token(value: Any, where: str) -> str:
    text = _text(value, where)
    if not _TOKEN_RE.fullmatch(text) or len(text.encode("utf-8")) > MAX_TOKEN_BYTES_V1:
        _fail(f"{where} must be printable ASCII of at most {MAX_TOKEN_BYTES_V1} bytes")
    return text


def _root(value: Any, where: str) -> str:
    if not _ROOT_RE.fullmatch(_text(value, where)):
        _fail(f"{where} must be a lowercase 0x-prefixed 32-byte hex root")
    return str(value)


def _atoms(value: Any, where: str) -> int:
    text = _text(value, where)
    if not _ATOMS_RE.fullmatch(text) or int(text) > MAX_ATOMS_V1:
        _fail(f"{where} must be a canonical unsigned base-10 atom string below 2^128")
    return int(text)


def _positive_atoms(value: Any, where: str) -> int:
    atoms = _atoms(value, where)
    if atoms == 0:
        _fail(f"{where} must be omitted rather than carry a zero balance")
    return atoms


def _flag(value: Any, where: str) -> bool:
    if type(value) is not bool:
        _fail(f"{where} must be a JSON boolean")
    return value


def _boolean(expected: bool, reason: str) -> Parser:
    def parse(value: Any, where: str) -> bool:
        if _flag(value, where) is not expected:
            _fail(f"{where} must be {str(expected).lower()} {reason}")
        return expected

    return parse


def _epoch(value: Any, where: str) -> int:
    if type(value) is not int:
        _fail(f"{where} must be a JSON integer with exact int type")
    if not 0 <= value <= MAX_WRITER_EPOCH_V1:
        _fail(f"{where} must lie in [0, {MAX_WRITER_EPOCH_V1}]")
    return value


def _member(allowed: tuple[str, ...], noun: str) -> Parser:
    def parse(value: Any, where: str) -> str:
        text = _text(value, where)
        if text not in allowed:
            _fail(f"{where} is not a declared {noun}: expected one of {sorted(allowed)}")
        return text

    return parse


_true: Final[Parser] = _boolean(True, "for a rejection")
_false: Final[Parser] = _boolean(False, "for research-only evidence")
_schema: Final[Parser] = _member((CORPUS_SCHEMA_V1,), "corpus schema")
_reject_code: Final[Parser] = _member(REJECT_PRECEDENCE_V1, "reject code")
_custody_domain: Final[Parser] = _member((CUSTODY_DOMAIN_V1,), "custody domain")
_fee_owner_role: Final[Parser] = _member(FEE_OWNER_ROLES_V1, "fee owner role")
_defect_status: Final[Parser] = _member((DEFECT_KILLED_V1,), "prior defect status")


def _list(value: Any, where: str) -> list[Any]:
    if type(value) is not list:
        _fail(f"{where} must be a JSON array")
    return value


def _exact_json_value(value: Any, where: str) -> Any:
    """Reject Python-only container/scalar aliases outside the decoded JSON domain."""

    if type(value) in (str, int, bool) or value is None:
        return value
    if type(value) is list:
        return [
            _exact_json_value(item, f"{where}[{index}]")
            for index, item in enumerate(value)
        ]
    if type(value) is dict:
        if any(type(key) is not str for key in value):
            _fail(f"{where} must use exact JSON string keys")
        return {
            key: _exact_json_value(item, f"{where}.{key}")
            for key, item in value.items()
        }
    _fail(f"{where} must contain exact JSON values")


def _each(parse: Parser) -> Parser:
    def parse_all(value: Any, where: str) -> tuple[Any, ...]:
        return tuple(parse(item, f"{where}[{i}]") for i, item in enumerate(_list(value, where)))

    return parse_all


_texts: Final[Parser] = _each(_text)


def _tokens(value: Any, where: str) -> tuple[str, ...]:
    items: tuple[str, ...] = _texts(value, where)
    if not items or items != tuple(sorted(set(items))):
        _fail(f"{where} must be a nonempty array of tokens, sorted and unique")
    return tuple(_token(item, where) for item in items)


def _empty_outbox(value: Any, where: str) -> tuple[()]:
    if _list(value, where):
        _fail(f"{where} must stay empty for this lane")
    return ()


def _fields(spec: Mapping[str, Parser]) -> Parser:
    """Build a parser for a closed JSON object: exactly these keys, exactly typed."""

    def parse(value: Any, where: str) -> dict[str, Any]:
        if type(value) is not dict:
            _fail(f"{where} must be a JSON object")
        if tuple(sorted(value)) != tuple(sorted(spec)):
            _fail(f"{where} must carry exactly the fields {sorted(spec)}")
        return {key: field(value[key], f"{where}.{key}") for key, field in spec.items()}

    return parse


def _rows_of(spec: Mapping[str, Parser]) -> Parser:
    return _each(_fields(spec))


_CONTEXT_SPEC: Final[dict[str, Parser]] = {
    "chain_id": _token, "subject_id": _token, "writer_epoch": _epoch,
    "command_occurrence_id": _root, "deployment_root": _root, "grant_root": _root,
    "module_release_id": _root, "profile_root": _root,
}
_COMMAND_SPEC: Final[dict[str, Parser]] = {
    "amount_atoms": _atoms, "asset": _token, "command_kind": _token,
    "max_fee_atoms": _atoms, "recipient": _token, "sender": _token,
}
_STATE_SPEC: Final[dict[str, Parser]] = {
    "module_release_id": _root,
    "balances": _rows_of({
        "amount_atoms": _positive_atoms, "asset": _token,
        "custody_domain": _custody_domain, "owner": _token,
    }),
    "policies": _rows_of(
        {"asset": _token, "enabled": _flag, "fee_owner": _token, "transfer_fee_atoms": _atoms}
    ),
    "supplies": _rows_of({"amount_atoms": _atoms, "asset": _token}),
}
_REJECTED_SPEC: Final[dict[str, Parser]] = {
    "effects_empty": _true, "outcome": _text,
    "reject_code": _reject_code, "state_root_unchanged": _true,
}
# The accepted expectation deliberately carries no inner row schema:
# `_parse_case` pins every row, field, type and canonical spelling by
# exact equality against the independently recomputed observation.
_ACCEPTED_SPEC: Final[dict[str, Parser]] = dict.fromkeys(
    ("asset_conservation", "effect_rows", "fee_conservation", "occurrence_consumptions",
     "post_balances"),
    _exact_json_value,
) | {"external_outbox_enqueue": _empty_outbox, "outcome": _text}


@dataclass(frozen=True, slots=True)
class RefinementPolicyV1:
    asset: str
    fee_owner: str
    transfer_fee_atoms: int
    enabled: bool


@dataclass(frozen=True, slots=True)
class RefinementPreStateV1:
    module_release_id: str
    policies: tuple[RefinementPolicyV1, ...]
    balances: Mapping[tuple[str, str], int]
    supplies: Mapping[str, int]

    def policy_for(self, asset: str) -> RefinementPolicyV1 | None:
        return next((policy for policy in self.policies if policy.asset == asset), None)

    def account_total(self, asset: str) -> int:
        return sum(atoms for (row_asset, _), atoms in self.balances.items() if row_asset == asset)


@dataclass(frozen=True, slots=True)
class RefinementCaseV1:
    case_id: str
    title: str
    classes: tuple[str, ...]
    fee_owner_role: str
    precedence_pair: tuple[str, str] | None
    context: Mapping[str, Any]
    pre_state: Mapping[str, Any]
    command: Mapping[str, Any]
    expected: Mapping[str, Any]
    parsed_pre_state: RefinementPreStateV1

    @property
    def outcome(self) -> str:
        return str(self.expected["outcome"])

    @property
    def reject_code(self) -> str | None:
        code = self.expected.get("reject_code")
        return None if code is None else str(code)


@dataclass(frozen=True, slots=True)
class AssetTransferRefinementCorpusV1:
    validation_command: str
    unreachable_codes: Mapping[str, str]
    deterministic_replay_repetitions: int
    checked_observations: tuple[str, ...]
    nonclaims: tuple[str, ...]
    prior_defects: tuple[Mapping[str, Any], ...]
    cases: tuple[RefinementCaseV1, ...]


def _parse_pre_state(raw: Any, where: str) -> RefinementPreStateV1:
    state = _fields(_STATE_SPEC)(raw, where)
    policies = tuple(
        RefinementPolicyV1(row["asset"], row["fee_owner"], row["transfer_fee_atoms"], row["enabled"])
        for row in state["policies"]
    )
    assets = tuple(policy.asset for policy in policies)
    if not assets or assets != tuple(sorted(set(assets))):
        _fail(f"{where}.policies must be nonempty and sorted and unique by asset")
    supplies = {row["asset"]: row["amount_atoms"] for row in state["supplies"]}
    if tuple(supplies) != assets or len(state["supplies"]) != len(assets):
        _fail(f"{where}.supplies must cover exactly the policy assets in policy order")
    keys = [(row["asset"], row["owner"], row["custody_domain"]) for row in state["balances"]]
    if keys != sorted(set(keys)):
        _fail(f"{where}.balances must be sorted and unique by (asset, owner, custody_domain)")
    balances = {(row["asset"], row["owner"]): row["amount_atoms"] for row in state["balances"]}
    if any(asset not in supplies for asset, _ in balances):
        _fail(f"{where}.balances carries an asset with no lane policy")
    for asset, supply_atoms in supplies.items():
        if sum(a for (row_asset, _), a in balances.items() if row_asset == asset) > supply_atoms:
            _fail(f"{where} account total for {asset!r} exceeds supply")
    proxies = (MappingProxyType(balances), MappingProxyType(supplies))
    return RefinementPreStateV1(state["module_release_id"], policies, *proxies)


def _parse_expected(raw: Any, where: str) -> dict[str, Any]:
    if type(raw) is not dict:
        _fail(f"{where} must be a JSON object")
    outcome = _text(raw.get("outcome"), f"{where}.outcome")
    if outcome not in ("accepted", "rejected"):
        _fail(f"{where}.outcome must be 'accepted' or 'rejected'")
    return _fields(_REJECTED_SPEC if outcome == "rejected" else _ACCEPTED_SPEC)(raw, where)


def _parse_precedence_pair(value: Any, where: str) -> tuple[str, str] | None:
    if value is None:
        return None
    entries: tuple[str, ...] = _each(_reject_code)(value, where)
    if len(entries) != 2:
        _fail(f"{where} must name exactly two reject codes")
    first, second = entries
    if REJECT_PRECEDENCE_V1.index(second) - REJECT_PRECEDENCE_V1.index(first) != 1:
        _fail(f"{where} must name adjacent reject classes")
    return (first, second)


_CASE_SPEC: Final[dict[str, Parser]] = {
    "case_id": _token, "title": _text, "classes": _tokens,
    "command": _fields(_COMMAND_SPEC), "context": _fields(_CONTEXT_SPEC),
    "expected": _parse_expected, "fee_owner_role": _fee_owner_role,
    "precedence_pair": _parse_precedence_pair, "pre_state": _parse_pre_state,
}
_CORPUS_SPEC: Final[dict[str, Parser]] = {
    "authority": _fields(dict.fromkeys(
        ("migration_authority", "production_authority", "proof_authority", "release_authority",
         "settlement_authority", "value_movement_authority"), _false)),
    "scalar_encoding": _fields(dict.fromkeys(
        ("atom_fields", "boolean_fields", "delta_fields", "root_fields", "small_integer_fields"),
        _text)),
    "prior_defects": _rows_of(
        {"defect": _text, "regression_case_ids": _tokens, "status": _defect_status}
    ),
    "unreachable_codes": _rows_of({"code": _reject_code, "reason": _text}),
    "cases": _list, "checked_observations": _tokens, "class_vocabulary": _tokens,
    "corpus_version": _epoch, "deterministic_replay_repetitions": _epoch,
    "nonclaims": _texts, "regeneration": _text, "reject_precedence": _texts,
    "required_boundary_classes": _tokens, "required_fee_owner_roles": _tokens,
    "schema": _schema, "validation_command": _text,
}


def _aggregated_deltas(
    command: Mapping[str, Any], policy: RefinementPolicyV1
) -> tuple[tuple[str, ...], dict[str, int]]:
    """Aggregate every role delta before any signed 128-bit width check."""

    sender, recipient = str(command["sender"]), str(command["recipient"])
    amount, fee = int(command["amount_atoms"]), policy.transfer_fee_atoms
    deltas = {sender: -(amount + fee), recipient: amount}
    deltas[policy.fee_owner] = deltas.get(policy.fee_owner, 0) + fee
    order = [sender]
    if recipient != sender:
        order.append(recipient)
    if policy.fee_owner not in order:
        order.append(policy.fee_owner)
    return tuple(order), deltas


def violated_codes_v1(case: RefinementCaseV1) -> frozenset[str]:
    """Independently name every reject condition the case violates at once."""

    context, state, command = case.context, case.parsed_pre_state, case.command
    asset, amount = str(command["asset"]), int(command["amount_atoms"])
    policy = state.policy_for(asset)
    fee = 0 if policy is None else policy.transfer_fee_atoms
    violated = {
        code
        for code, hit in (
            ("RELEASE_MISMATCH", context["module_release_id"] != state.module_release_id),
            ("UNKNOWN_COMMAND", command["command_kind"] != COMMAND_KIND_V1),
            ("UNKNOWN_ASSET", policy is None),
            ("DISABLED_ASSET", policy is not None and not policy.enabled),
            ("UNAUTHORIZED_SUBJECT", command["sender"] != context["subject_id"]),
            ("SELF_TRANSFER", command["sender"] == command["recipient"]),
            ("ZERO_AMOUNT", amount == 0),
            ("FEE_LIMIT_EXCEEDED", policy is not None and fee > int(command["max_fee_atoms"])),
        )
        if hit
    }
    # An unknown asset, a self transfer and a zero amount leave no role deltas to
    # aggregate, and each already outranks every width or balance class below.
    if policy is None or violated & {"SELF_TRANSFER", "ZERO_AMOUNT"}:
        return frozenset(violated)
    order, deltas = _aggregated_deltas(command, policy)
    widths = (*deltas.values(), fee)
    if any(width < MIN_DELTA_ATOMS_V1 or width > MAX_DELTA_ATOMS_V1 for width in widths):
        violated.add("EFFECT_DELTA_OVERFLOW")
    for owner in order:
        post = state.balances.get((asset, owner), 0) + deltas[owner]
        if post < 0:
            violated.add("INSUFFICIENT_BALANCE")
        elif post > MAX_ATOMS_V1:
            violated.add("BALANCE_OVERFLOW")
    return frozenset(violated)


def _accepted_observation(case: RefinementCaseV1, policy: RefinementPolicyV1) -> dict[str, Any]:
    state, command = case.parsed_pre_state, case.command
    asset, fee = str(command["asset"]), policy.transfer_fee_atoms
    order, deltas = _aggregated_deltas(command, policy)
    post = dict(state.balances)
    for owner in order:
        value = post.pop((asset, owner), 0) + deltas[owner]
        if value:
            post[(asset, owner)] = value
    rows = [
        {"kind": ACCOUNT_MOVEMENT_V1, "principal": owner, "asset": asset,
         "custody_domain": CUSTODY_DOMAIN_V1, "delta_atoms": str(delta)}
        for owner, delta in deltas.items()
        if delta
    ]
    if fee:
        rows.append({"kind": FEE_ALLOCATION_V1, "principal": policy.fee_owner, "asset": asset,
                     "custody_domain": CUSTODY_DOMAIN_V1, "delta_atoms": str(fee)})
    rows.sort(key=lambda row: (row["kind"], row["asset"], row["principal"], row["custody_domain"]))
    fee_rows = [{"asset": asset, "fee_charged_atoms": str(fee),
                 "current_allocations_atoms": str(fee), "carried_residue_atoms": "0"}]
    supply = str(state.supplies[asset])
    post_total = sum(atoms for (row_asset, _), atoms in post.items() if row_asset == asset)
    return {
        "outcome": "accepted",
        "post_balances": [
            {"owner": owner, "asset": row_asset, "custody_domain": CUSTODY_DOMAIN_V1,
             "amount_atoms": str(atoms)}
            for (row_asset, owner), atoms in sorted(post.items())
        ],
        "effect_rows": rows,
        "fee_conservation": fee_rows if fee else [],
        "asset_conservation": {
            "asset": asset, "owned_and_custodied_pre_atoms": str(state.account_total(asset)),
            "owned_and_custodied_post_atoms": str(post_total),
            "supply_pre_atoms": supply, "supply_post_atoms": supply,
            "authorized_issue_atoms": "0", "authorized_burn_atoms": "0",
        },
        "occurrence_consumptions": [str(case.context["command_occurrence_id"])],
        "external_outbox_enqueue": [],
    }


def intended_observation_v1(case: RefinementCaseV1) -> dict[str, Any]:
    """Recompute the intended observation from the recorded inputs alone."""

    violated = violated_codes_v1(case)
    if (first := next((code for code in REJECT_PRECEDENCE_V1 if code in violated), None)) is not None:
        return {"outcome": "rejected", "reject_code": first,
                "effects_empty": True, "state_root_unchanged": True}
    policy = case.parsed_pre_state.policy_for(str(case.command["asset"]))
    if policy is None:
        _fail(f"case {case.case_id!r} has no lane policy yet violates no reject condition")
    return _accepted_observation(case, policy)


def _implied_fee_owner_role(command: Mapping[str, Any], state: RefinementPreStateV1) -> str:
    policy = state.policy_for(str(command["asset"]))
    if policy is None:
        return "none"
    is_sender = policy.fee_owner == command["sender"]
    is_recipient = policy.fee_owner == command["recipient"]
    if is_sender and is_recipient:
        _fail("fee owner alias is ambiguous: sender, recipient and fee owner coincide")
    if is_sender:
        return "sender"
    return "recipient" if is_recipient else "distinct"


def _parse_case(raw: Any, index: int, vocabulary: tuple[str, ...], unreachable: Mapping[str, str]) -> RefinementCaseV1:
    """Parse one case, then confront it with the independently recomputed oracle."""

    fields = _fields(_CASE_SPEC)(raw, f"cases[{index}]")
    where = f"case {fields['case_id']!r}"
    unknown = tuple(name for name in fields["classes"] if name not in vocabulary)
    if unknown:
        _fail(f"{where}.classes uses aliases outside the closed vocabulary: {list(unknown)}")
    if (fields["precedence_pair"] is not None) != ("precedence_pair" in fields["classes"]):
        _fail(f"{where} must declare the precedence_pair class exactly when it carries a pair")
    if fields["fee_owner_role"] != _implied_fee_owner_role(fields["command"], fields["pre_state"]):
        _fail(f"{where}.fee_owner_role does not match the fee owner alias implied by the inputs")
    case = RefinementCaseV1(
        case_id=fields["case_id"], title=fields["title"], classes=fields["classes"],
        fee_owner_role=fields["fee_owner_role"], precedence_pair=fields["precedence_pair"],
        context=MappingProxyType(fields["context"]), command=MappingProxyType(fields["command"]),
        pre_state=MappingProxyType(dict(raw["pre_state"])),
        expected=MappingProxyType(dict(raw["expected"])), parsed_pre_state=fields["pre_state"],
    )
    intended = intended_observation_v1(case)
    if intended != dict(case.expected):
        _fail(f"{where} expectation drifts from the independent oracle: {intended}")
    if case.reject_code in unreachable:
        _fail(f"{where} expects {case.reject_code}, which the corpus declares unreachable")
    if case.precedence_pair is not None:
        first, second = case.precedence_pair
        if case.reject_code != first:
            _fail(f"{where}.precedence_pair must lead with the recorded reject code")
        if case.precedence_pair in MUTUALLY_EXCLUSIVE_PAIRS_V1:
            if all(policy.enabled for policy in case.parsed_pre_state.policies):
                _fail(f"{where} must carry a disabled-policy lure for the {second} half of the pair")
        elif second not in violated_codes_v1(case):
            _fail(f"{where} must violate {second} as well as {first}")
    return case


def _check_corpus_coverage(
    cases: tuple[RefinementCaseV1, ...], corpus: Mapping[str, Any], unreachable: Mapping[str, str]
) -> None:
    used = {name for case in cases for name in case.classes}
    absent = tuple(name for name in corpus["required_boundary_classes"] if name not in used)
    if absent:
        _fail(f"corpus is missing required boundary classes: {list(absent)}")
    dead = tuple(name for name in corpus["class_vocabulary"] if name not in used)
    if dead:
        _fail(f"corpus.class_vocabulary carries unused aliases: {list(dead)}")
    codes, pairs = {c.reject_code for c in cases}, {c.precedence_pair for c in cases}
    for code in REJECT_PRECEDENCE_V1:
        if code not in unreachable and code not in codes:
            _fail(f"reject code {code} is neither covered by a case nor declared unreachable")
    for pair in zip(REJECT_PRECEDENCE_V1[:-1], REJECT_PRECEDENCE_V1[1:], strict=True):
        # A pair whose second code is declared unreachable over this bounded corpus has no
        # constructible discriminator here; its runtime reachability is witnessed by the
        # suite the unreachable_codes row names (Opus P30 NEW-5).
        if pair[1] in unreachable:
            continue
        if pair not in pairs:
            _fail(f"adjacent precedence pair {pair} has no witness case")
    roles = {case.fee_owner_role for case in cases if case.outcome == "accepted"}
    missing = tuple(role for role in corpus["required_fee_owner_roles"] if role not in roles)
    if missing:
        _fail(f"corpus lacks accepted fee owner roles: {list(missing)}")
    known = {case.case_id for case in cases}
    for defect in corpus["prior_defects"]:
        lost = tuple(name for name in defect["regression_case_ids"] if name not in known)
        if lost:
            _fail(f"prior defect {defect['defect']!r} lost its regression cases: {list(lost)}")


def parse_asset_transfer_refinement_corpus_v1(payload: Any) -> AssetTransferRefinementCorpusV1:
    """Parse and fully validate a refinement corpus payload, failing closed."""

    corpus = _fields(_CORPUS_SPEC)(payload, "corpus")
    if corpus["corpus_version"] != 1:
        _fail("corpus.corpus_version must be 1")
    if "check_asset_transfer_refinement_v1.py" not in corpus["validation_command"]:
        _fail("corpus.validation_command must name this oracle")
    if corpus["reject_precedence"] != REJECT_PRECEDENCE_V1:
        _fail("corpus.reject_precedence must equal the scoped precedence encoded by this oracle")
    if corpus["checked_observations"] != REQUIRED_OBSERVATIONS_V1:
        _fail("corpus.checked_observations must equal the closed observation set")
    if corpus["required_fee_owner_roles"] != tuple(sorted(ACCEPTED_FEE_OWNER_ROLES_V1)):
        _fail("corpus.required_fee_owner_roles must require distinct, recipient and sender")
    if not 2 <= corpus["deterministic_replay_repetitions"] <= 16:
        _fail("corpus.deterministic_replay_repetitions must lie in [2, 16]")
    if len(corpus["nonclaims"]) < 4:
        _fail("corpus.nonclaims must state at least four explicit nonclaims")
    if not corpus["prior_defects"]:
        _fail("corpus.prior_defects must record the defects this corpus keeps dead")
    vocabulary = corpus["class_vocabulary"]
    escaped = tuple(name for name in corpus["required_boundary_classes"] if name not in vocabulary)
    if escaped:
        _fail(f"corpus.required_boundary_classes escapes the vocabulary: {list(escaped)}")
    unreachable: dict[str, str] = {}
    for row in corpus["unreachable_codes"]:
        if row["code"] in unreachable:
            _fail(f"corpus.unreachable_codes declares {row['code']} unreachable twice")
        unreachable[row["code"]] = row["reason"]

    cases: list[RefinementCaseV1] = []
    seen: set[str] = set()
    for index, raw_case in enumerate(corpus["cases"]):
        case = _parse_case(raw_case, index, vocabulary, unreachable)
        if case.case_id in seen:
            _fail(f"duplicate case id: {case.case_id}")
        seen.add(case.case_id)
        cases.append(case)
    _check_corpus_coverage(tuple(cases), corpus, unreachable)
    return AssetTransferRefinementCorpusV1(
        validation_command=corpus["validation_command"],
        unreachable_codes=MappingProxyType(unreachable),
        deterministic_replay_repetitions=corpus["deterministic_replay_repetitions"],
        checked_observations=corpus["checked_observations"], nonclaims=corpus["nonclaims"],
        prior_defects=tuple(MappingProxyType(row) for row in corpus["prior_defects"]),
        cases=tuple(cases),
    )


def load_asset_transfer_refinement_corpus_v1(path: Path = CORPUS_PATH) -> AssetTransferRefinementCorpusV1:
    """Read and validate the corpus file, failing closed on duplicate JSON keys."""

    try:
        payload = json.loads(
            path.read_text(encoding="utf-8"), object_pairs_hook=_reject_duplicate_keys
        )
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        _fail(f"corpus cannot be loaded: {type(exc).__name__}: {exc}")
    return parse_asset_transfer_refinement_corpus_v1(payload)


def check_asset_transfer_refinement_v1(corpus_path: Path = CORPUS_PATH) -> dict[str, object]:
    findings: list[str] = []
    corpus: AssetTransferRefinementCorpusV1 | None = None
    try:
        corpus = load_asset_transfer_refinement_corpus_v1(corpus_path)
    except RefinementCorpusErrorV1 as exc:
        findings.append(str(exc))
    cases = () if corpus is None else corpus.cases
    defects = () if corpus is None else corpus.prior_defects
    return {
        "schema": CHECK_SCHEMA_V1, "ok": not findings, "findings": findings,
        "corpus_path": str(corpus_path), "case_count": len(cases),
        "accepted_cases": sum(1 for case in cases if case.outcome == "accepted"),
        "rejected_cases": sum(1 for case in cases if case.outcome == "rejected"),
        "prior_defect_regressions": sorted({n for d in defects for n in d["regression_case_ids"]}),
        "unreachable_codes": [] if corpus is None else sorted(corpus.unreachable_codes),
        "validation_command": None if corpus is None else corpus.validation_command,
        "production_authority": False,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Validate the ASSET_TRANSFER refinement corpus.")
    parser.add_argument("--corpus", type=Path, default=CORPUS_PATH)
    args = parser.parse_args(argv)
    report = check_asset_transfer_refinement_v1(args.corpus)
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
