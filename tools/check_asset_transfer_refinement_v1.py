#!/usr/bin/env python3
"""Independent oracle for the bounded `ASSET_TRANSFER` refinement corpus.

This module is deliberately standalone: it never imports or calls either runtime
transition, and it recomputes every expected observation in
``tests/data/asset_transfer_refinement_v1.json`` from the recorded
context/pre-state/command under the scoped rejection precedence

    RELEASE_MISMATCH -> UNKNOWN_COMMAND -> UNKNOWN_ASSET -> DISABLED_ASSET ->
    UNAUTHORIZED_SUBJECT -> SELF_TRANSFER -> ZERO_AMOUNT -> FEE_LIMIT_EXCEEDED ->
    EFFECT_DELTA_OVERFLOW -> sender insufficiency ->
    recipient/distinct-fee-owner BALANCE_OVERFLOW

with account deltas aggregated before any signed 128-bit width check.

Authority: bounded executable research evidence only. Nothing here creates
production, settlement, release, migration, proof, or value-moving authority,
and ``custody_domain`` is an accounting-location/control-domain label rather
than a claim of possession or legal title.
"""

from __future__ import annotations

import argparse
import json
import re
from collections.abc import Mapping, Sequence
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

MAX_ATOMS_V1: Final = (1 << 128) - 1
MIN_DELTA_ATOMS_V1: Final = -(1 << 127)
MAX_DELTA_ATOMS_V1: Final = (1 << 127) - 1
MAX_WRITER_EPOCH_V1: Final = (1 << 64) - 1
MAX_TOKEN_BYTES_V1: Final = 160

REJECT_PRECEDENCE_V1: Final = (
    "RELEASE_MISMATCH",
    "UNKNOWN_COMMAND",
    "UNKNOWN_ASSET",
    "DISABLED_ASSET",
    "UNAUTHORIZED_SUBJECT",
    "SELF_TRANSFER",
    "ZERO_AMOUNT",
    "FEE_LIMIT_EXCEEDED",
    "EFFECT_DELTA_OVERFLOW",
    "INSUFFICIENT_BALANCE",
    "BALANCE_OVERFLOW",
)
# `UNKNOWN_ASSET` and `DISABLED_ASSET` cannot be violated by one command at once,
# so their pairwise witness carries a disabled-policy lure instead.
MUTUALLY_EXCLUSIVE_PAIRS_V1: Final = (("UNKNOWN_ASSET", "DISABLED_ASSET"),)
CROSS_LANGUAGE_VALUES_V1: Final = ("agree", "rust_defect_pending_repair")
FEE_OWNER_ROLES_V1: Final = ("distinct", "none", "recipient", "sender")
ACCEPTED_FEE_OWNER_ROLES_V1: Final = ("distinct", "recipient", "sender")
REQUIRED_OBSERVATIONS_V1: Final = (
    "accepted_asset_conservation",
    "accepted_effect_rows",
    "accepted_empty_external_outbox",
    "accepted_fee_conservation",
    "accepted_lane_write_pre_post_binding",
    "accepted_occurrence_consumptions",
    "accepted_post_balances",
    "deterministic_repeated_replay",
    "rejection_code",
    "rejection_empty_effect_plan",
    "rejection_pre_post_root_equality",
)

_CORPUS_KEYS: Final = (
    "authority",
    "cases",
    "checked_observations",
    "class_vocabulary",
    "corpus_version",
    "deterministic_replay_repetitions",
    "nonclaims",
    "regeneration",
    "reject_precedence",
    "required_boundary_classes",
    "required_fee_owner_roles",
    "scalar_encoding",
    "schema",
    "unreachable_codes",
    "validation_command",
)
_AUTHORITY_KEYS: Final = (
    "migration_authority",
    "production_authority",
    "proof_authority",
    "release_authority",
    "settlement_authority",
    "value_movement_authority",
)
_SCALAR_ENCODING_KEYS: Final = (
    "atom_fields",
    "boolean_fields",
    "delta_fields",
    "root_fields",
    "small_integer_fields",
)
_UNREACHABLE_KEYS: Final = ("code", "reason")
_CASE_KEYS: Final = (
    "case_id",
    "classes",
    "command",
    "context",
    "cross_language",
    "expected",
    "fee_owner_role",
    "precedence_pair",
    "pre_state",
    "rust_observed_code",
    "title",
)
_CONTEXT_KEYS: Final = (
    "chain_id",
    "command_occurrence_id",
    "deployment_root",
    "grant_root",
    "module_release_id",
    "profile_root",
    "subject_id",
    "writer_epoch",
)
_STATE_KEYS: Final = ("balances", "module_release_id", "policies", "supplies")
_POLICY_KEYS: Final = ("asset", "enabled", "fee_owner", "transfer_fee_atoms")
_BALANCE_KEYS: Final = ("amount_atoms", "asset", "custody_domain", "owner")
_SUPPLY_KEYS: Final = ("amount_atoms", "asset")
_COMMAND_KEYS: Final = (
    "amount_atoms",
    "asset",
    "command_kind",
    "max_fee_atoms",
    "recipient",
    "sender",
)
_ACCEPTED_KEYS: Final = (
    "asset_conservation",
    "effect_rows",
    "external_outbox_enqueue",
    "fee_conservation",
    "occurrence_consumptions",
    "outcome",
    "post_balances",
)
_REJECTED_KEYS: Final = ("effects_empty", "outcome", "reject_code", "state_root_unchanged")
_EFFECT_ROW_KEYS: Final = ("asset", "custody_domain", "delta_atoms", "kind", "principal")
_FEE_ROW_KEYS: Final = (
    "asset",
    "carried_residue_atoms",
    "current_allocations_atoms",
    "fee_charged_atoms",
)
_CONSERVATION_KEYS: Final = (
    "asset",
    "authorized_burn_atoms",
    "authorized_issue_atoms",
    "owned_and_custodied_post_atoms",
    "owned_and_custodied_pre_atoms",
    "supply_post_atoms",
    "supply_pre_atoms",
)

_ATOMS_RE: Final = re.compile(r"\A(?:0|[1-9][0-9]*)\Z")
_DELTA_RE: Final = re.compile(r"\A(?:0|-?[1-9][0-9]*)\Z")
_ROOT_RE: Final = re.compile(r"\A0x[0-9a-f]{64}\Z")


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


def _mapping(value: object, *, keys: Sequence[str], where: str) -> Mapping[str, Any]:
    if type(value) is not dict:
        _fail(f"{where} must be a JSON object")
    if tuple(sorted(value)) != tuple(sorted(keys)):
        _fail(f"{where} must carry exactly the fields {sorted(keys)}")
    return value


def _list(value: object, *, where: str) -> list[Any]:
    if type(value) is not list:
        _fail(f"{where} must be a JSON array")
    return value


def _text(value: object, *, where: str) -> str:
    if type(value) is not str:
        _fail(f"{where} must be a JSON string")
    if not value:
        _fail(f"{where} must not be empty")
    return value


def _token(value: object, *, where: str) -> str:
    text = _text(value, where=where)
    if len(text.encode("utf-8")) > MAX_TOKEN_BYTES_V1:
        _fail(f"{where} exceeds {MAX_TOKEN_BYTES_V1} UTF-8 bytes")
    if any(ord(char) < 0x21 or ord(char) > 0x7E for char in text):
        _fail(f"{where} must use printable ASCII")
    return text


def _root(value: object, *, where: str) -> str:
    text = _text(value, where=where)
    if not _ROOT_RE.fullmatch(text):
        _fail(f"{where} must be a lowercase 0x-prefixed 32-byte hex root")
    return text


def _atoms(value: object, *, where: str) -> int:
    text = _text(value, where=where)
    if not _ATOMS_RE.fullmatch(text):
        _fail(f"{where} must be a canonical unsigned base-10 atom string")
    atoms = int(text)
    if atoms > MAX_ATOMS_V1:
        _fail(f"{where} must fit an unsigned 128-bit integer")
    return atoms


def _delta(value: object, *, where: str) -> int:
    text = _text(value, where=where)
    if not _DELTA_RE.fullmatch(text):
        _fail(f"{where} must be a canonical signed base-10 delta string")
    delta = int(text)
    if not MIN_DELTA_ATOMS_V1 <= delta <= MAX_DELTA_ATOMS_V1:
        _fail(f"{where} must fit a signed 128-bit integer")
    return delta


def _flag(value: object, *, where: str) -> bool:
    if type(value) is not bool:
        _fail(f"{where} must be a JSON boolean")
    return value


def _small_int(value: object, *, where: str, maximum: int) -> int:
    if type(value) is not int:
        _fail(f"{where} must be a JSON integer with exact int type")
    if not 0 <= value <= maximum:
        _fail(f"{where} must lie in [0, {maximum}]")
    return value


def _sorted_unique_tokens(value: object, *, where: str) -> tuple[str, ...]:
    items = tuple(_token(item, where=f"{where} entry") for item in _list(value, where=where))
    if not items:
        _fail(f"{where} must not be empty")
    if items != tuple(sorted(set(items))):
        _fail(f"{where} must be sorted and unique")
    return items


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
    cross_language: str
    fee_owner_role: str
    precedence_pair: tuple[str, str] | None
    rust_observed_code: str | None
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
    schema: str
    corpus_version: int
    validation_command: str
    regeneration: str
    reject_precedence: tuple[str, ...]
    unreachable_codes: Mapping[str, str]
    deterministic_replay_repetitions: int
    required_fee_owner_roles: tuple[str, ...]
    class_vocabulary: tuple[str, ...]
    required_boundary_classes: tuple[str, ...]
    checked_observations: tuple[str, ...]
    nonclaims: tuple[str, ...]
    cases: tuple[RefinementCaseV1, ...]


def _parse_pre_state(raw: object, *, where: str) -> RefinementPreStateV1:
    state = _mapping(raw, keys=_STATE_KEYS, where=where)
    policies: list[RefinementPolicyV1] = []
    for index, row in enumerate(_list(state["policies"], where=f"{where}.policies")):
        marker = f"{where}.policies[{index}]"
        fields = _mapping(row, keys=_POLICY_KEYS, where=marker)
        policies.append(
            RefinementPolicyV1(
                asset=_token(fields["asset"], where=f"{marker}.asset"),
                fee_owner=_token(fields["fee_owner"], where=f"{marker}.fee_owner"),
                transfer_fee_atoms=_atoms(
                    fields["transfer_fee_atoms"], where=f"{marker}.transfer_fee_atoms"
                ),
                enabled=_flag(fields["enabled"], where=f"{marker}.enabled"),
            )
        )
    assets = tuple(policy.asset for policy in policies)
    if not assets:
        _fail(f"{where}.policies must not be empty")
    if assets != tuple(sorted(set(assets))):
        _fail(f"{where}.policies must be sorted and unique by asset")

    supplies: dict[str, int] = {}
    supply_rows = _list(state["supplies"], where=f"{where}.supplies")
    for index, row in enumerate(supply_rows):
        marker = f"{where}.supplies[{index}]"
        fields = _mapping(row, keys=_SUPPLY_KEYS, where=marker)
        supplies[_token(fields["asset"], where=f"{marker}.asset")] = _atoms(
            fields["amount_atoms"], where=f"{marker}.amount_atoms"
        )
    if tuple(supplies) != assets or len(supply_rows) != len(assets):
        _fail(f"{where}.supplies must cover exactly the policy assets in policy order")

    balances: dict[tuple[str, str], int] = {}
    previous_key: tuple[str, str, str] | None = None
    for index, row in enumerate(_list(state["balances"], where=f"{where}.balances")):
        marker = f"{where}.balances[{index}]"
        fields = _mapping(row, keys=_BALANCE_KEYS, where=marker)
        owner = _token(fields["owner"], where=f"{marker}.owner")
        asset = _token(fields["asset"], where=f"{marker}.asset")
        domain = _token(fields["custody_domain"], where=f"{marker}.custody_domain")
        atoms = _atoms(fields["amount_atoms"], where=f"{marker}.amount_atoms")
        if domain != CUSTODY_DOMAIN_V1:
            _fail(f"{marker}.custody_domain must be {CUSTODY_DOMAIN_V1!r}")
        if atoms == 0:
            _fail(f"{marker} must be omitted rather than carry a zero balance")
        if asset not in supplies:
            _fail(f"{marker}.asset has no lane policy")
        key = (asset, owner, domain)
        if previous_key is not None and previous_key >= key:
            _fail(f"{where}.balances must be sorted and unique by (asset, owner, custody_domain)")
        previous_key = key
        balances[(asset, owner)] = atoms

    for asset, supply_atoms in supplies.items():
        total = sum(atoms for (row_asset, _), atoms in balances.items() if row_asset == asset)
        if total > supply_atoms:
            _fail(f"{where} account total for {asset!r} exceeds supply")

    return RefinementPreStateV1(
        module_release_id=_root(state["module_release_id"], where=f"{where}.module_release_id"),
        policies=tuple(policies),
        balances=MappingProxyType(balances),
        supplies=MappingProxyType(supplies),
    )


def _parse_context(raw: object, *, where: str) -> Mapping[str, Any]:
    context = _mapping(raw, keys=_CONTEXT_KEYS, where=where)
    _token(context["chain_id"], where=f"{where}.chain_id")
    _token(context["subject_id"], where=f"{where}.subject_id")
    _small_int(context["writer_epoch"], where=f"{where}.writer_epoch", maximum=MAX_WRITER_EPOCH_V1)
    for field in ("deployment_root", "profile_root", "module_release_id", "command_occurrence_id", "grant_root"):
        _root(context[field], where=f"{where}.{field}")
    return context


def _parse_command(raw: object, *, where: str) -> Mapping[str, Any]:
    command = _mapping(raw, keys=_COMMAND_KEYS, where=where)
    for field in ("command_kind", "asset", "sender", "recipient"):
        _token(command[field], where=f"{where}.{field}")
    _atoms(command["amount_atoms"], where=f"{where}.amount_atoms")
    _atoms(command["max_fee_atoms"], where=f"{where}.max_fee_atoms")
    return command


def _aggregated_deltas(
    command: Mapping[str, Any], policy: RefinementPolicyV1
) -> tuple[tuple[str, ...], dict[str, int]]:
    """Aggregate every role delta before any signed 128-bit width check."""

    sender = str(command["sender"])
    recipient = str(command["recipient"])
    amount = int(str(command["amount_atoms"]))
    fee = policy.transfer_fee_atoms
    deltas = {sender: -(amount + fee), recipient: amount}
    deltas[policy.fee_owner] = deltas.get(policy.fee_owner, 0) + fee
    order = [sender]
    if recipient != sender:
        order.append(recipient)
    if policy.fee_owner not in order:
        order.append(policy.fee_owner)
    return tuple(order), deltas


def _post_balance(state: RefinementPreStateV1, asset: str, owner: str, delta: int) -> int:
    return state.balances.get((asset, owner), 0) + delta


def violated_codes_v1(case: RefinementCaseV1) -> frozenset[str]:
    """Independently name every reject condition the case violates at once."""

    context, state, command = case.context, case.parsed_pre_state, case.command
    asset = str(command["asset"])
    amount = int(str(command["amount_atoms"]))
    policy = state.policy_for(asset)
    violated: set[str] = set()
    if context["module_release_id"] != state.module_release_id:
        violated.add("RELEASE_MISMATCH")
    if command["command_kind"] != COMMAND_KIND_V1:
        violated.add("UNKNOWN_COMMAND")
    if policy is None:
        violated.add("UNKNOWN_ASSET")
    elif not policy.enabled:
        violated.add("DISABLED_ASSET")
    if command["sender"] != context["subject_id"]:
        violated.add("UNAUTHORIZED_SUBJECT")
    if command["sender"] == command["recipient"]:
        violated.add("SELF_TRANSFER")
    if amount == 0:
        violated.add("ZERO_AMOUNT")
    if policy is None:
        return frozenset(violated)
    if policy.transfer_fee_atoms > int(str(command["max_fee_atoms"])):
        violated.add("FEE_LIMIT_EXCEEDED")
    if command["sender"] == command["recipient"] or amount == 0:
        return frozenset(violated)
    order, deltas = _aggregated_deltas(command, policy)
    widths = (*deltas.values(), policy.transfer_fee_atoms)
    if any(width < MIN_DELTA_ATOMS_V1 or width > MAX_DELTA_ATOMS_V1 for width in widths):
        violated.add("EFFECT_DELTA_OVERFLOW")
    for owner in order:
        post = _post_balance(state, asset, owner, deltas[owner])
        if post < 0:
            violated.add("INSUFFICIENT_BALANCE")
        elif post > MAX_ATOMS_V1:
            violated.add("BALANCE_OVERFLOW")
    return frozenset(violated)


def intended_observation_v1(case: RefinementCaseV1) -> dict[str, Any]:
    """Recompute the intended observation from the recorded inputs alone."""

    context, state, command = case.context, case.parsed_pre_state, case.command
    asset = str(command["asset"])
    amount = int(str(command["amount_atoms"]))

    def rejected(code: str) -> dict[str, Any]:
        return {
            "outcome": "rejected",
            "reject_code": code,
            "effects_empty": True,
            "state_root_unchanged": True,
        }

    if context["module_release_id"] != state.module_release_id:
        return rejected("RELEASE_MISMATCH")
    if command["command_kind"] != COMMAND_KIND_V1:
        return rejected("UNKNOWN_COMMAND")
    policy = state.policy_for(asset)
    if policy is None:
        return rejected("UNKNOWN_ASSET")
    if not policy.enabled:
        return rejected("DISABLED_ASSET")
    if command["sender"] != context["subject_id"]:
        return rejected("UNAUTHORIZED_SUBJECT")
    if command["sender"] == command["recipient"]:
        return rejected("SELF_TRANSFER")
    if amount == 0:
        return rejected("ZERO_AMOUNT")
    if policy.transfer_fee_atoms > int(str(command["max_fee_atoms"])):
        return rejected("FEE_LIMIT_EXCEEDED")

    order, deltas = _aggregated_deltas(command, policy)
    widths = (*deltas.values(), policy.transfer_fee_atoms)
    if any(width < MIN_DELTA_ATOMS_V1 or width > MAX_DELTA_ATOMS_V1 for width in widths):
        return rejected("EFFECT_DELTA_OVERFLOW")

    post_atoms = dict(state.balances)
    for owner in order:
        value = post_atoms.get((asset, owner), 0) + deltas[owner]
        if value < 0:
            return rejected("INSUFFICIENT_BALANCE")
        if value > MAX_ATOMS_V1:
            return rejected("BALANCE_OVERFLOW")
        if value == 0:
            post_atoms.pop((asset, owner), None)
        else:
            post_atoms[(asset, owner)] = value

    fee = policy.transfer_fee_atoms
    rows = [
        {
            "kind": ACCOUNT_MOVEMENT_V1,
            "principal": owner,
            "asset": asset,
            "custody_domain": CUSTODY_DOMAIN_V1,
            "delta_atoms": str(delta),
        }
        for owner, delta in deltas.items()
        if delta != 0
    ]
    if fee:
        rows.append(
            {
                "kind": FEE_ALLOCATION_V1,
                "principal": policy.fee_owner,
                "asset": asset,
                "custody_domain": CUSTODY_DOMAIN_V1,
                "delta_atoms": str(fee),
            }
        )
    rows.sort(key=lambda row: (row["kind"], row["asset"], row["principal"], row["custody_domain"]))
    return {
        "outcome": "accepted",
        "post_balances": [
            {
                "owner": owner,
                "asset": row_asset,
                "custody_domain": CUSTODY_DOMAIN_V1,
                "amount_atoms": str(atoms),
            }
            for (row_asset, owner), atoms in sorted(post_atoms.items())
        ],
        "effect_rows": rows,
        "fee_conservation": (
            [
                {
                    "asset": asset,
                    "fee_charged_atoms": str(fee),
                    "current_allocations_atoms": str(fee),
                    "carried_residue_atoms": "0",
                }
            ]
            if fee
            else []
        ),
        "asset_conservation": {
            "asset": asset,
            "owned_and_custodied_pre_atoms": str(state.account_total(asset)),
            "owned_and_custodied_post_atoms": str(
                sum(atoms for (row_asset, _), atoms in post_atoms.items() if row_asset == asset)
            ),
            "supply_pre_atoms": str(state.supplies[asset]),
            "supply_post_atoms": str(state.supplies[asset]),
            "authorized_issue_atoms": "0",
            "authorized_burn_atoms": "0",
        },
        "occurrence_consumptions": [str(context["command_occurrence_id"])],
        "external_outbox_enqueue": [],
    }


def _parse_expected(raw: object, *, where: str, precedence: tuple[str, ...]) -> Mapping[str, Any]:
    if type(raw) is not dict:
        _fail(f"{where} must be a JSON object")
    outcome = _text(raw.get("outcome"), where=f"{where}.outcome")
    if outcome == "rejected":
        expected = _mapping(raw, keys=_REJECTED_KEYS, where=where)
        code = _text(expected["reject_code"], where=f"{where}.reject_code")
        if code not in precedence:
            _fail(f"{where}.reject_code is not a declared reject code")
        if not _flag(expected["effects_empty"], where=f"{where}.effects_empty"):
            _fail(f"{where}.effects_empty must be true for a rejection")
        if not _flag(expected["state_root_unchanged"], where=f"{where}.state_root_unchanged"):
            _fail(f"{where}.state_root_unchanged must be true for a rejection")
        return expected
    if outcome != "accepted":
        _fail(f"{where}.outcome must be 'accepted' or 'rejected'")
    expected = _mapping(raw, keys=_ACCEPTED_KEYS, where=where)
    for index, row in enumerate(_list(expected["post_balances"], where=f"{where}.post_balances")):
        marker = f"{where}.post_balances[{index}]"
        fields = _mapping(row, keys=_BALANCE_KEYS, where=marker)
        _token(fields["owner"], where=f"{marker}.owner")
        _token(fields["asset"], where=f"{marker}.asset")
        _token(fields["custody_domain"], where=f"{marker}.custody_domain")
        if _atoms(fields["amount_atoms"], where=f"{marker}.amount_atoms") == 0:
            _fail(f"{marker} must be omitted rather than carry a zero balance")
    for index, row in enumerate(_list(expected["effect_rows"], where=f"{where}.effect_rows")):
        marker = f"{where}.effect_rows[{index}]"
        fields = _mapping(row, keys=_EFFECT_ROW_KEYS, where=marker)
        if _text(fields["kind"], where=f"{marker}.kind") not in (
            ACCOUNT_MOVEMENT_V1,
            FEE_ALLOCATION_V1,
        ):
            _fail(f"{marker}.kind is outside the corpus effect vocabulary")
        _token(fields["principal"], where=f"{marker}.principal")
        _token(fields["asset"], where=f"{marker}.asset")
        _token(fields["custody_domain"], where=f"{marker}.custody_domain")
        if _delta(fields["delta_atoms"], where=f"{marker}.delta_atoms") == 0:
            _fail(f"{marker}.delta_atoms must be nonzero")
    for index, row in enumerate(
        _list(expected["fee_conservation"], where=f"{where}.fee_conservation")
    ):
        marker = f"{where}.fee_conservation[{index}]"
        fields = _mapping(row, keys=_FEE_ROW_KEYS, where=marker)
        _token(fields["asset"], where=f"{marker}.asset")
        for field in ("fee_charged_atoms", "current_allocations_atoms", "carried_residue_atoms"):
            _atoms(fields[field], where=f"{marker}.{field}")
    conservation = _mapping(
        expected["asset_conservation"], keys=_CONSERVATION_KEYS, where=f"{where}.asset_conservation"
    )
    _token(conservation["asset"], where=f"{where}.asset_conservation.asset")
    for field in _CONSERVATION_KEYS[1:]:
        _atoms(conservation[field], where=f"{where}.asset_conservation.{field}")
    for index, value in enumerate(
        _list(expected["occurrence_consumptions"], where=f"{where}.occurrence_consumptions")
    ):
        _root(value, where=f"{where}.occurrence_consumptions[{index}]")
    if _list(expected["external_outbox_enqueue"], where=f"{where}.external_outbox_enqueue"):
        _fail(f"{where}.external_outbox_enqueue must stay empty for this lane")
    return expected


def _fee_owner_role(case_command: Mapping[str, Any], state: RefinementPreStateV1) -> str:
    policy = state.policy_for(str(case_command["asset"]))
    if policy is None:
        return "none"
    is_sender = policy.fee_owner == case_command["sender"]
    is_recipient = policy.fee_owner == case_command["recipient"]
    if is_sender and is_recipient:
        _fail("fee owner alias is ambiguous: sender, recipient and fee owner coincide")
    if is_sender:
        return "sender"
    if is_recipient:
        return "recipient"
    return "distinct"


def _parse_case(
    raw: object, *, index: int, vocabulary: tuple[str, ...], precedence: tuple[str, ...]
) -> RefinementCaseV1:
    where = f"cases[{index}]"
    fields = _mapping(raw, keys=_CASE_KEYS, where=where)
    case_id = _token(fields["case_id"], where=f"{where}.case_id")
    where = f"case {case_id!r}"
    classes = _sorted_unique_tokens(fields["classes"], where=f"{where}.classes")
    unknown = tuple(name for name in classes if name not in vocabulary)
    if unknown:
        _fail(f"{where}.classes uses aliases outside the closed vocabulary: {list(unknown)}")
    cross_language = _text(fields["cross_language"], where=f"{where}.cross_language")
    if cross_language not in CROSS_LANGUAGE_VALUES_V1:
        _fail(f"{where}.cross_language must be one of {list(CROSS_LANGUAGE_VALUES_V1)}")

    context = _parse_context(fields["context"], where=f"{where}.context")
    parsed_pre_state = _parse_pre_state(fields["pre_state"], where=f"{where}.pre_state")
    command = _parse_command(fields["command"], where=f"{where}.command")
    expected = _parse_expected(fields["expected"], where=f"{where}.expected", precedence=precedence)

    role = _text(fields["fee_owner_role"], where=f"{where}.fee_owner_role")
    if role not in FEE_OWNER_ROLES_V1:
        _fail(f"{where}.fee_owner_role must be one of {list(FEE_OWNER_ROLES_V1)}")
    if role != _fee_owner_role(command, parsed_pre_state):
        _fail(f"{where}.fee_owner_role does not match the fee owner alias implied by the inputs")

    pair_value = fields["precedence_pair"]
    pair: tuple[str, str] | None = None
    if pair_value is not None:
        entries = tuple(
            _text(entry, where=f"{where}.precedence_pair entry")
            for entry in _list(pair_value, where=f"{where}.precedence_pair")
        )
        if len(entries) != 2:
            _fail(f"{where}.precedence_pair must name exactly two reject codes")
        pair = (entries[0], entries[1])
    if (pair is not None) != ("precedence_pair" in classes):
        _fail(f"{where} must declare the precedence_pair class exactly when it carries a pair")

    observed = fields["rust_observed_code"]
    rust_observed_code: str | None = None
    if observed is not None:
        rust_observed_code = _text(observed, where=f"{where}.rust_observed_code")
        if rust_observed_code not in precedence:
            _fail(f"{where}.rust_observed_code is not a declared reject code")
    if (rust_observed_code is not None) != (cross_language == "rust_defect_pending_repair"):
        _fail(f"{where}.rust_observed_code must be set exactly for a recorded Rust defect")

    return RefinementCaseV1(
        case_id=case_id,
        title=_text(fields["title"], where=f"{where}.title"),
        classes=classes,
        cross_language=cross_language,
        fee_owner_role=role,
        precedence_pair=pair,
        rust_observed_code=rust_observed_code,
        context=MappingProxyType(dict(context)),
        pre_state=MappingProxyType(dict(fields["pre_state"])),
        command=MappingProxyType(dict(command)),
        expected=MappingProxyType(dict(expected)),
        parsed_pre_state=parsed_pre_state,
    )


def _check_case_semantics(case: RefinementCaseV1, unreachable: Mapping[str, str]) -> None:
    where = f"case {case.case_id!r}"
    intended = intended_observation_v1(case)
    if intended != dict(case.expected):
        _fail(f"{where} expectation drifts from the independent oracle: {intended}")
    violated = violated_codes_v1(case)
    if case.outcome == "rejected":
        first = next(code for code in REJECT_PRECEDENCE_V1 if code in violated)
        if first != case.reject_code:
            _fail(f"{where} precedence scan yields {first} but the corpus records {case.reject_code}")
        if case.reject_code in unreachable:
            _fail(f"{where} expects {case.reject_code}, which the corpus declares unreachable")
    elif violated:
        _fail(f"{where} is recorded as accepted but violates {sorted(violated)}")
    if case.rust_observed_code is not None and case.rust_observed_code == case.reject_code:
        _fail(f"{where}.rust_observed_code must differ from the intended reject code")

    if case.precedence_pair is None:
        return
    first, second = case.precedence_pair
    if first not in REJECT_PRECEDENCE_V1 or second not in REJECT_PRECEDENCE_V1:
        _fail(f"{where}.precedence_pair names an undeclared reject code")
    if REJECT_PRECEDENCE_V1.index(second) - REJECT_PRECEDENCE_V1.index(first) != 1:
        _fail(f"{where}.precedence_pair must name adjacent reject classes")
    if case.reject_code != first:
        _fail(f"{where}.precedence_pair must lead with the recorded reject code")
    if (first, second) in MUTUALLY_EXCLUSIVE_PAIRS_V1:
        if all(policy.enabled for policy in case.parsed_pre_state.policies):
            _fail(f"{where} must carry a disabled-policy lure for the {second} half of the pair")
        return
    if second not in violated:
        _fail(f"{where} must violate {second} as well as {first}")


def parse_asset_transfer_refinement_corpus_v1(payload: object) -> AssetTransferRefinementCorpusV1:
    """Parse and fully validate a refinement corpus payload, failing closed."""

    corpus = _mapping(payload, keys=_CORPUS_KEYS, where="corpus")
    if corpus["schema"] != CORPUS_SCHEMA_V1:
        _fail(f"corpus.schema must be {CORPUS_SCHEMA_V1!r}")
    if _small_int(corpus["corpus_version"], where="corpus.corpus_version", maximum=1) != 1:
        _fail("corpus.corpus_version must be 1")
    authority = _mapping(corpus["authority"], keys=_AUTHORITY_KEYS, where="corpus.authority")
    for field in _AUTHORITY_KEYS:
        if _flag(authority[field], where=f"corpus.authority.{field}"):
            _fail(f"corpus.authority.{field} must be false for research-only evidence")
    _mapping(corpus["scalar_encoding"], keys=_SCALAR_ENCODING_KEYS, where="corpus.scalar_encoding")
    validation_command = _text(corpus["validation_command"], where="corpus.validation_command")
    if "check_asset_transfer_refinement_v1.py" not in validation_command:
        _fail("corpus.validation_command must name this oracle")
    regeneration = _text(corpus["regeneration"], where="corpus.regeneration")

    precedence = tuple(
        _text(code, where="corpus.reject_precedence entry")
        for code in _list(corpus["reject_precedence"], where="corpus.reject_precedence")
    )
    if precedence != REJECT_PRECEDENCE_V1:
        _fail("corpus.reject_precedence must equal the scoped precedence encoded by this oracle")

    unreachable: dict[str, str] = {}
    for index, row in enumerate(_list(corpus["unreachable_codes"], where="corpus.unreachable_codes")):
        marker = f"corpus.unreachable_codes[{index}]"
        fields = _mapping(row, keys=_UNREACHABLE_KEYS, where=marker)
        code = _text(fields["code"], where=f"{marker}.code")
        if code not in precedence:
            _fail(f"{marker}.code is not a declared reject code")
        if code in unreachable:
            _fail(f"{marker}.code is declared unreachable twice")
        unreachable[code] = _text(fields["reason"], where=f"{marker}.reason")

    repetitions = _small_int(
        corpus["deterministic_replay_repetitions"],
        where="corpus.deterministic_replay_repetitions",
        maximum=16,
    )
    if repetitions < 2:
        _fail("corpus.deterministic_replay_repetitions must be at least 2")

    roles = _sorted_unique_tokens(
        corpus["required_fee_owner_roles"], where="corpus.required_fee_owner_roles"
    )
    if roles != tuple(sorted(ACCEPTED_FEE_OWNER_ROLES_V1)):
        _fail("corpus.required_fee_owner_roles must require distinct, recipient and sender")

    vocabulary = _sorted_unique_tokens(corpus["class_vocabulary"], where="corpus.class_vocabulary")
    required = _sorted_unique_tokens(
        corpus["required_boundary_classes"], where="corpus.required_boundary_classes"
    )
    missing_vocabulary = tuple(name for name in required if name not in vocabulary)
    if missing_vocabulary:
        _fail(f"corpus.required_boundary_classes escapes the vocabulary: {list(missing_vocabulary)}")
    observations = _sorted_unique_tokens(
        corpus["checked_observations"], where="corpus.checked_observations"
    )
    if observations != REQUIRED_OBSERVATIONS_V1:
        _fail("corpus.checked_observations must equal the closed observation set")
    nonclaims = tuple(
        _text(claim, where="corpus.nonclaims entry")
        for claim in _list(corpus["nonclaims"], where="corpus.nonclaims")
    )
    if len(nonclaims) < 4:
        _fail("corpus.nonclaims must state at least four explicit nonclaims")

    raw_cases = _list(corpus["cases"], where="corpus.cases")
    if not raw_cases:
        _fail("corpus.cases must not be empty")
    cases: list[RefinementCaseV1] = []
    seen: set[str] = set()
    for index, raw_case in enumerate(raw_cases):
        case = _parse_case(raw_case, index=index, vocabulary=vocabulary, precedence=precedence)
        if case.case_id in seen:
            _fail(f"duplicate case id: {case.case_id}")
        seen.add(case.case_id)
        _check_case_semantics(case, unreachable)
        cases.append(case)

    used_classes = {name for case in cases for name in case.classes}
    absent = tuple(name for name in required if name not in used_classes)
    if absent:
        _fail(f"corpus is missing required boundary classes: {list(absent)}")
    dead = tuple(name for name in vocabulary if name not in used_classes)
    if dead:
        _fail(f"corpus.class_vocabulary carries unused aliases: {list(dead)}")

    covered_codes = {case.reject_code for case in cases if case.reject_code is not None}
    for code in precedence:
        if code in unreachable:
            continue
        if code not in covered_codes:
            _fail(f"reject code {code} is neither covered by a case nor declared unreachable")
    covered_pairs = {case.precedence_pair for case in cases if case.precedence_pair is not None}
    for first, second in zip(precedence[:-1], precedence[1:], strict=True):
        if (first, second) not in covered_pairs:
            _fail(f"adjacent precedence pair ({first}, {second}) has no witness case")

    accepted_roles = {case.fee_owner_role for case in cases if case.outcome == "accepted"}
    missing_roles = tuple(role for role in roles if role not in accepted_roles)
    if missing_roles:
        _fail(f"corpus lacks accepted fee owner roles: {list(missing_roles)}")
    if not any(case.cross_language == "rust_defect_pending_repair" for case in cases):
        _fail("corpus must retain the recorded cross-language counterexample")

    return AssetTransferRefinementCorpusV1(
        schema=CORPUS_SCHEMA_V1,
        corpus_version=1,
        validation_command=validation_command,
        regeneration=regeneration,
        reject_precedence=precedence,
        unreachable_codes=MappingProxyType(unreachable),
        deterministic_replay_repetitions=repetitions,
        required_fee_owner_roles=roles,
        class_vocabulary=vocabulary,
        required_boundary_classes=required,
        checked_observations=observations,
        nonclaims=nonclaims,
        cases=tuple(cases),
    )


def load_asset_transfer_refinement_corpus_v1(
    corpus_path: Path = CORPUS_PATH,
) -> AssetTransferRefinementCorpusV1:
    """Read and validate the corpus file, failing closed on duplicate JSON keys."""

    try:
        payload = json.loads(
            corpus_path.read_text(encoding="utf-8"), object_pairs_hook=_reject_duplicate_keys
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
    return {
        "schema": CHECK_SCHEMA_V1,
        "ok": not findings,
        "findings": findings,
        "corpus_path": str(corpus_path),
        "case_count": 0 if corpus is None else len(corpus.cases),
        "accepted_cases": 0
        if corpus is None
        else sum(1 for case in corpus.cases if case.outcome == "accepted"),
        "rejected_cases": 0
        if corpus is None
        else sum(1 for case in corpus.cases if case.outcome == "rejected"),
        "cross_language_counterexamples": []
        if corpus is None
        else sorted(
            case.case_id
            for case in corpus.cases
            if case.cross_language == "rust_defect_pending_repair"
        ),
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
