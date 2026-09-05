"""Executable runtime-to-model differential for the V2 managed-asset leaf.

`Proofs.ManagedAssetLifecycleRefinementV2` proves properties of a bounded model
of `transition_managed_asset_lifecycle_v2`.  `tests/formal/
test_lean_asset_lane_refinement_v2.py` compiles that model, checks its axioms,
and pins the SHA-256 of the Python sources it describes.  Neither one runs the
model, so a model that drifted from the source could still carry every proof
and every pin.

This gate closes that: it compiles `Proofs.ManagedAssetRuntimeParityV2`,
evaluates its report, and compares the report against the live Python leaf on a
fixed table of thirty-seven scenarios.

What is compared
----------------

For every scenario the two sides must agree on the complete modeled outcome:

* the verdict, and for a rejection its exact code;
* the post supply, the post projected account-row total, and the post balance of
  every enumerated principal;
* the lane-write arity and its pre-to-post orientation;
* the occurrence-consumption arity and identity;
* the external-outbox arity and the zero external roots;
* whether an effect payload exists at all;
* for accepted scenarios, the effect payload: moved principal, account delta,
  supply-effect kind, supply delta, and all six conservation fields.

A rejection is additionally required to be a byte-level no-op on the Python
side: the canonical encoding of the pre-state and its state root are unchanged
across the call, and the rejection reports `pre_state_root == post_state_root`.

The stateful history threads one state through eight steps that interleave
accepted and rejected transitions and replays an already-consumed occurrence.

What the evidence is
--------------------

This is a bounded differential over a finite enumerated corpus, evaluated
against two separately written implementations of the same decision.  Be exact
about what that independence is worth: the Lean model was written from the
Python source, so agreement is evidence that the two have not *drifted*, not
evidence that either matches an external specification.  A shared
misunderstanding of the intended semantics would be invisible here.

It is not a refinement proof of the Python source: nothing here quantifies over
all inputs, and a defect confined to inputs outside the table would survive it.
Three fixed semantic mutants are carried in the Lean module and shown to be
killed by the Python runtime, which bounds how weak the corpus can be with
respect to those three specific clauses, and nothing more.

The abstraction map between the two scenario tables is itself checked, not
assumed.  The report emits, per scenario, the modeled literals and the twenty
one *relations between opaque root tokens* the model actually reads.  This test
recomputes those same relations from its own Python objects and requires
agreement, so a Lean vector that silently stopped encoding the situation its
Python twin encodes fails here.  Recomputing a guard *input* is not the same as
recomputing a guard *decision*: every verdict, post state, and effect compared
above comes from the two implementations, never from this file.

Non-claims
----------

Root values, occurrence identifiers, and command-body digests are opaque
equality tokens in the model.  No hash, digest, or canonical-codec equivalence
is claimed, and the report carries no root value.  The modeled state has one
registered asset; multi-asset states, canonical row ordering, resource
ceilings, the writer epoch, the module journal, the receipt root, registry and
release/profile authentication, coordinator mounting, settlement, publication,
migration, and production authority are all outside this evidence.  The leaf
models no replay guard and the history shows the runtime has none either; that
is recorded as an observation about this leaf, not as a claim that replay is
handled somewhere else.
"""

from __future__ import annotations

import os
import re
import shutil
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Final

import pytest

from src.core.asset_transfer_types_v2 import (
    ACCOUNT_CUSTODY_DOMAIN_V2,
    AssetClassV2,
)
from src.core.global_economic_proof_v2 import EconomicCommandOccurrenceV2
from src.core.global_settlement_types_v2 import (
    MAX_ATOMS_V2,
    MAX_DELTA_ATOMS_V2,
    MIN_DELTA_ATOMS_V2,
    ZERO_ROOT_V2,
    AssetSupplyV2,
    EconomicAmountV2,
    EconomicEffectKindV2,
    LaneIdV2,
    LaneWriteV2,
    canonical_global_bytes_v2,
)
from src.core.managed_asset_lifecycle_module_v2 import (
    transition_managed_asset_lifecycle_v2,
)
from src.core.managed_asset_lifecycle_result_v2 import (
    ManagedAssetLifecycleRejectCodeV2,
)
from src.core.managed_asset_lifecycle_types_v2 import (
    MANAGED_ASSET_BURN_COMMAND_KIND_V2,
    MANAGED_ASSET_ISSUE_COMMAND_KIND_V2,
    ManagedAssetLifecycleAcceptedV2,
    ManagedAssetLifecycleCommandV2,
    ManagedAssetLifecycleContextV2,
    ManagedAssetLifecyclePolicyV2,
    ManagedAssetLifecycleRejectedV2,
    ManagedAssetLifecycleResultV2,
    ManagedAssetLifecycleStateV2,
)

ROOT = Path(__file__).resolve().parents[2]
LEAN_DIR = ROOT / "lean-mathlib"
ASSET_PROOF = LEAN_DIR / "Proofs" / "AssetTransferRefinementV2.lean"
MANAGED_PROOF = LEAN_DIR / "Proofs" / "ManagedAssetLifecycleRefinementV2.lean"
PARITY_PROOF = LEAN_DIR / "Proofs" / "ManagedAssetRuntimeParityV2.lean"
SCANNER = ROOT / "tools" / "scan_lean_proof_placeholders_v1.py"

PARITY_NAMESPACE = "Proofs.ManagedAssetRuntimeParityV2"
PINNED_TOOLCHAIN = "leanprover/lean4:v4.27.0"
ALLOWED_STANDARD_AXIOMS = frozenset({"propext", "Quot.sound", "Classical.choice"})

# Hand-maintained claim surface: every name is a `theorem` in the parity module
# and every name is passed to `#print axioms`.  Nothing else is claimed.
PARITY_THEOREMS = (
    "parity_accepted_iff_no_reject",
    "parity_totality",
    "parity_rejected_post_eq_pre",
    "parity_rejected_effects_empty",
    "parity_accepted_conservation",
    "parity_accepted_consumes_exact_occurrence",
    "parity_accepted_burn_authority",
    "firstFailingBool_eq_firstFailing",
    "m1_kill_vector_exists",
    "m2_kill_vector_exists",
    "m3_kill_vector_exists",
    "mutant_M1_is_live",
    "mutant_M1_divergence_is_exactly_that_list",
    "mutant_M2_is_live",
    "mutant_M2_divergence_is_exactly_that_list",
    "mutant_M2_leaves_the_issuer_owned_burn_alias_alone",
    "mutant_M3_is_live",
    "mutant_M3_touches_only_the_supply_post_field",
    "vector_names_are_unique",
    "table_produces_every_code_except_the_two_unreachable_ones",
    "unreachable_codes_are_absent_from_the_table",
    "table_contains_accepted_vectors",
)

# The repository forbids these in proof sources; `native_decide` would move the
# kernel's work into compiled code and is excluded by the same convention.
FORBIDDEN_PROOF_TOKENS = ("sorry", "admit", "native_decide", "axiom ")

REPORTED_PRINCIPALS = ("alice", "bob", "issuer", "mallory")
MODELED_ASSET = "ORD"

U128_MAX = (1 << 128) - 1
I128_MAX = (1 << 127) - 1
I128_MIN = -(1 << 127)


def _root(value: int) -> str:
    return f"0x{value:064x}"


# The abstraction map for opaque tokens.  Only this file needs it; the report
# carries relations between tokens, never token values.
TOKEN_ROOTS: dict[str, str] = {
    "release-v2": _root(0x11),
    "release-v3": _root(0x12),
    "global-pre": _root(0x21),
    "global-pre-other": _root(0x22),
    "origin-ord": _root(0x31),
    "origin-eur": _root(0x32),
    "origin-zdex": _root(0x33),
    "issue-grant": _root(0x41),
    "burn-grant": _root(0x42),
    "foreign-grant": _root(0x43),
}

# Occurrence fields the bounded model does not carry.  They are fixed so they
# cannot influence any compared outcome.
UNMODELED_CHAIN_ID = "zeno-v2-parity"
UNMODELED_DEPLOYMENT_ROOT = _root(0x51)
UNMODELED_ROUTE_RELEASE_ID = _root(0x52)
UNMODELED_PROFILE_ROOT = _root(0x53)
UNMODELED_WRITER_EPOCH = 7


def _token_root(token: str | None) -> str | None:
    if token is None:
        return None
    return TOKEN_ROOTS[token]


def _policy(
    *,
    asset: str = MODELED_ASSET,
    asset_class: AssetClassV2 = AssetClassV2.REGISTERED_ORDINARY_TOKEN,
    origin: str | None = "origin-ord",
    issue_subject: str | None = "issuer",
    issue_grant: str | None = "issue-grant",
    burn_grant: str | None = "burn-grant",
    enabled: bool = True,
) -> ManagedAssetLifecyclePolicyV2:
    return ManagedAssetLifecyclePolicyV2(
        asset=asset,
        asset_class=asset_class,
        asset_origin_root=_token_root(origin),
        atom_decimals=8,
        issue_authority_subject=issue_subject,
        issue_authorization_root=_token_root(issue_grant),
        burn_authorization_root=_token_root(burn_grant),
        enabled=enabled,
    )


def _state(
    policy: ManagedAssetLifecyclePolicyV2,
    rows: tuple[tuple[str, int], ...],
    supply: int,
) -> ManagedAssetLifecycleStateV2:
    balances = tuple(
        sorted(
            (
                EconomicAmountV2(owner, policy.asset, ACCOUNT_CUSTODY_DOMAIN_V2, amount)
                for owner, amount in rows
            ),
            key=lambda row: row.key,
        )
    )
    return ManagedAssetLifecycleStateV2(
        module_release_id=TOKEN_ROOTS["release-v2"],
        policies=(policy,),
        balances=balances,
        supplies=(AssetSupplyV2(policy.asset, supply),),
    )


_DEFAULT_AUTHORIZATION: Final = "<default>"


def _command(
    *,
    kind: str,
    owner: str,
    amount: int,
    asset: str = MODELED_ASSET,
    asset_class: AssetClassV2 = AssetClassV2.REGISTERED_ORDINARY_TOKEN,
    origin: str | None = "origin-ord",
    authorization: str | None = _DEFAULT_AUTHORIZATION,
) -> ManagedAssetLifecycleCommandV2:
    if authorization == _DEFAULT_AUTHORIZATION:
        authorization = (
            "issue-grant" if kind == MANAGED_ASSET_ISSUE_COMMAND_KIND_V2 else "burn-grant"
        )
    return ManagedAssetLifecycleCommandV2(
        command_kind=kind,
        asset=asset,
        asset_class=asset_class,
        asset_origin_root=_token_root(origin),
        atom_decimals=8,
        authorization_root=_token_root(authorization),
        account_owner=owner,
        amount_atoms=amount,
    )


def _issue(owner: str, amount: int, **overrides: Any) -> ManagedAssetLifecycleCommandV2:
    return _command(
        kind=MANAGED_ASSET_ISSUE_COMMAND_KIND_V2, owner=owner, amount=amount, **overrides
    )


def _burn(owner: str, amount: int, **overrides: Any) -> ManagedAssetLifecycleCommandV2:
    return _command(
        kind=MANAGED_ASSET_BURN_COMMAND_KIND_V2, owner=owner, amount=amount, **overrides
    )


def _occurrence(
    *,
    command_kind: str,
    command_body_hash: str,
    subject: str,
    grant: str,
    nonce: int,
    global_pre: str = "global-pre",
    consumed: tuple[str, ...] = (),
) -> EconomicCommandOccurrenceV2:
    return EconomicCommandOccurrenceV2(
        chain_id=UNMODELED_CHAIN_ID,
        deployment_root=UNMODELED_DEPLOYMENT_ROOT,
        height=8,
        tx_index=0,
        op_index=0,
        command_kind=command_kind,
        command_body_hash=command_body_hash,
        route_release_id=UNMODELED_ROUTE_RELEASE_ID,
        subject_id=subject,
        grant_root=grant,
        nonce=nonce,
        profile_root=UNMODELED_PROFILE_ROOT,
        pre_state_root=TOKEN_ROOTS[global_pre],
        consumed_object_ids=consumed,
    )


def _context(
    occurrence: EconomicCommandOccurrenceV2 | None,
    *,
    release: str = "release-v2",
    global_pre: str = "global-pre",
) -> ManagedAssetLifecycleContextV2:
    return ManagedAssetLifecycleContextV2(
        writer_epoch=UNMODELED_WRITER_EPOCH,
        module_release_id=TOKEN_ROOTS[release],
        global_pre_state_root=TOKEN_ROOTS[global_pre],
        occurrence=occurrence,
    )


@dataclass(frozen=True)
class Twin:
    """One Python scenario paired with the Lean vector of the same name."""

    name: str
    occurrence_label: str
    state: ManagedAssetLifecycleStateV2
    context: ManagedAssetLifecycleContextV2
    command: ManagedAssetLifecycleCommandV2


def _authorized_twin(
    name: str,
    state: ManagedAssetLifecycleStateV2,
    command: ManagedAssetLifecycleCommandV2,
    nonce: int,
) -> Twin:
    """Mirror the Lean `scenarioOf`: an issue is presented by the policy subject
    with the issue grant, a burn by the account owner with the burn grant."""

    is_issue = command.command_kind == MANAGED_ASSET_ISSUE_COMMAND_KIND_V2
    subject = "issuer" if is_issue else command.account_owner
    grant = TOKEN_ROOTS["issue-grant" if is_issue else "burn-grant"]
    occurrence = _occurrence(
        command_kind=command.command_kind,
        command_body_hash=command.command_body_hash,
        subject=subject,
        grant=grant,
        nonce=nonce,
    )
    return Twin(name, f"occ:{name}", state, _context(occurrence), command)


_ORDINARY = AssetClassV2.REGISTERED_ORDINARY_TOKEN
_FUNDED_ROWS: tuple[tuple[str, int], ...] = (("alice", 10),)


def _build_twins() -> tuple[Twin, ...]:
    base = _policy()
    funded = _state(base, _FUNDED_ROWS, 10)
    empty = _state(base, (), 0)
    twins: list[Twin] = []
    counter = 0

    def authorized(
        name: str,
        state: ManagedAssetLifecycleStateV2,
        command: ManagedAssetLifecycleCommandV2,
    ) -> None:
        nonlocal counter
        counter += 1
        twins.append(_authorized_twin(name, state, command, counter))

    def explicit(
        name: str,
        state: ManagedAssetLifecycleStateV2,
        command: ManagedAssetLifecycleCommandV2,
        occurrence: EconomicCommandOccurrenceV2 | None,
        label: str,
        *,
        release: str = "release-v2",
        global_pre: str = "global-pre",
    ) -> None:
        twins.append(
            Twin(name, label, state, _context(occurrence, release=release, global_pre=global_pre), command)
        )

    # Accepted: issue, burn, row creation, row removal, owner-role aliases.
    authorized("issue_to_existing_holder", funded, _issue("alice", 7))
    authorized("issue_creates_new_row", funded, _issue("bob", 5))
    authorized("issue_one_atom", empty, _issue("alice", 1))
    authorized("issue_to_authority_subject_alias", funded, _issue("issuer", 3))
    authorized("burn_by_account_owner", funded, _burn("alice", 4))
    authorized("burn_removes_row_at_exact_balance", funded, _burn("alice", 10))
    authorized(
        "burn_by_owner_who_is_also_issuer_alias",
        _state(base, (("issuer", 9),), 9),
        _burn("issuer", 9),
    )

    # Accepted: width edges.
    authorized("issue_at_i128_max_delta", empty, _issue("alice", I128_MAX))
    authorized(
        "burn_at_negated_i128_min_delta",
        _state(base, (("alice", -I128_MIN),), -I128_MIN),
        _burn("alice", -I128_MIN),
    )
    authorized(
        "issue_to_exact_u128_supply_ceiling",
        _state(base, (("alice", U128_MAX - 1),), U128_MAX - 1),
        _issue("alice", 1),
    )

    # Rejected: occurrence binding and release.
    explicit("missing_occurrence", funded, _issue("alice", 7), None, "")
    issue_seven = _issue("alice", 7)
    explicit(
        "occurrence_pre_state_root_mismatch",
        funded,
        issue_seven,
        _occurrence(
            command_kind=issue_seven.command_kind,
            command_body_hash=issue_seven.command_body_hash,
            subject="issuer",
            grant=TOKEN_ROOTS["issue-grant"],
            nonce=101,
        ),
        "occ:pre-root",
        global_pre="global-pre-other",
    )
    explicit(
        "occurrence_consumes_object_ids",
        funded,
        issue_seven,
        _occurrence(
            command_kind=issue_seven.command_kind,
            command_body_hash=issue_seven.command_body_hash,
            subject="issuer",
            grant=TOKEN_ROOTS["issue-grant"],
            nonce=102,
            consumed=("object-1",),
        ),
        "occ:consumed",
    )
    explicit(
        "release_mismatch",
        funded,
        issue_seven,
        _occurrence(
            command_kind=issue_seven.command_kind,
            command_body_hash=issue_seven.command_body_hash,
            subject="issuer",
            grant=TOKEN_ROOTS["issue-grant"],
            nonce=103,
        ),
        "occ:release",
        release="release-v3",
    )

    # Rejected: command identity.
    freeze = _command(
        kind="managed_asset_freeze", owner="alice", amount=7, authorization="issue-grant"
    )
    explicit(
        "unknown_command_kind",
        funded,
        freeze,
        _occurrence(
            command_kind=freeze.command_kind,
            command_body_hash=freeze.command_body_hash,
            subject="issuer",
            grant=TOKEN_ROOTS["issue-grant"],
            nonce=104,
        ),
        "occ:unknown-kind",
    )
    explicit(
        "occurrence_kind_mismatch",
        funded,
        issue_seven,
        _occurrence(
            command_kind=MANAGED_ASSET_BURN_COMMAND_KIND_V2,
            command_body_hash=issue_seven.command_body_hash,
            subject="issuer",
            grant=TOKEN_ROOTS["issue-grant"],
            nonce=105,
        ),
        "occ:kind-swap",
    )
    explicit(
        "occurrence_body_mismatch",
        funded,
        issue_seven,
        _occurrence(
            command_kind=issue_seven.command_kind,
            command_body_hash=_issue("alice", 8).command_body_hash,
            subject="issuer",
            grant=TOKEN_ROOTS["issue-grant"],
            nonce=106,
        ),
        "occ:body-swap",
    )

    # Rejected: asset admission.
    authorized(
        "unknown_asset",
        funded,
        _issue("alice", 7, asset="EUR", origin="origin-eur"),
    )
    authorized(
        "disabled_asset", _state(_policy(enabled=False), _FUNDED_ROWS, 10), _issue("alice", 7)
    )
    authorized(
        "asset_class_mismatch",
        funded,
        _issue("alice", 7, asset_class=AssetClassV2.LP_SHARE),
    )
    authorized(
        "unregistered_asset",
        _state(_policy(origin=None), _FUNDED_ROWS, 10),
        _issue("alice", 7, origin=None),
    )
    authorized(
        "asset_origin_mismatch",
        funded,
        _issue("alice", 7, origin="origin-eur"),
    )
    authorized(
        "generic_authority_forbidden_for_protocol_asset",
        _state(
            _policy(
                asset="ZDEX",
                asset_class=AssetClassV2.ZDEX_PROTOCOL_TOKEN,
                origin="origin-zdex",
                issue_subject=None,
                issue_grant=None,
                burn_grant=None,
            ),
            (),
            0,
        ),
        _issue(
            "alice",
            7,
            asset="ZDEX",
            asset_class=AssetClassV2.ZDEX_PROTOCOL_TOKEN,
            origin="origin-zdex",
            authorization=None,
        ),
    )

    # Rejected: policy-bound authority.
    authorized(
        "issue_disabled",
        _state(_policy(issue_subject=None, issue_grant=None), _FUNDED_ROWS, 10),
        _issue("alice", 7),
    )
    authorized(
        "burn_disabled",
        _state(_policy(burn_grant=None), _FUNDED_ROWS, 10),
        _burn("alice", 4, authorization=None),
    )
    explicit(
        "issue_by_unauthorized_subject",
        funded,
        issue_seven,
        _occurrence(
            command_kind=issue_seven.command_kind,
            command_body_hash=issue_seven.command_body_hash,
            subject="mallory",
            grant=TOKEN_ROOTS["issue-grant"],
            nonce=107,
        ),
        "occ:bad-issuer",
    )
    burn_four = _burn("alice", 4)
    explicit(
        "burn_presented_by_non_owner",
        funded,
        burn_four,
        _occurrence(
            command_kind=burn_four.command_kind,
            command_body_hash=burn_four.command_body_hash,
            subject="mallory",
            grant=TOKEN_ROOTS["burn-grant"],
            nonce=108,
        ),
        "occ:bad-burner",
    )
    explicit(
        "burn_presented_by_policy_issuer_not_owner",
        funded,
        burn_four,
        _occurrence(
            command_kind=burn_four.command_kind,
            command_body_hash=burn_four.command_body_hash,
            subject="issuer",
            grant=TOKEN_ROOTS["burn-grant"],
            nonce=109,
        ),
        "occ:issuer-burns",
    )
    explicit(
        "occurrence_grant_root_mismatch",
        funded,
        issue_seven,
        _occurrence(
            command_kind=issue_seven.command_kind,
            command_body_hash=issue_seven.command_body_hash,
            subject="issuer",
            grant=TOKEN_ROOTS["foreign-grant"],
            nonce=110,
        ),
        "occ:bad-grant",
    )
    authorized(
        "command_authorization_root_mismatch",
        funded,
        _issue("alice", 7, authorization="foreign-grant"),
    )

    # Rejected: amount and width.
    authorized("zero_amount", funded, _issue("alice", 0))
    authorized(
        "issue_delta_overflow_at_i128_max_neighbor", empty, _issue("alice", I128_MAX + 1)
    )
    authorized(
        "burn_delta_overflow_at_i128_min_neighbor",
        _state(base, (("alice", U128_MAX),), U128_MAX),
        _burn("alice", -I128_MIN + 1),
    )

    # Rejected: post-stage supply and balance.
    authorized(
        "issue_supply_overflow_only",
        _state(base, (("bob", U128_MAX),), U128_MAX),
        _issue("alice", 1),
    )
    authorized(
        "issue_supply_and_balance_would_both_overflow",
        _state(base, (("alice", U128_MAX),), U128_MAX),
        _issue("alice", 1),
    )
    authorized("burn_exceeds_supply", _state(base, (("alice", 3),), 3), _burn("alice", 4))
    authorized(
        "burn_exceeds_owner_balance_with_supply_available",
        _state(base, (("alice", 1), ("bob", 8)), 10),
        _burn("alice", 2),
    )
    return tuple(twins)


@dataclass(frozen=True)
class HistoryStep:
    label: str
    occurrence_label: str
    context: ManagedAssetLifecycleContextV2
    command: ManagedAssetLifecycleCommandV2


def _build_history() -> tuple[ManagedAssetLifecycleStateV2, tuple[HistoryStep, ...]]:
    base = _policy()
    start = _state(base, (), 0)

    def authorized_step(
        label: str, command: ManagedAssetLifecycleCommandV2, occurrence_label: str, nonce: int
    ) -> HistoryStep:
        is_issue = command.command_kind == MANAGED_ASSET_ISSUE_COMMAND_KIND_V2
        occurrence = _occurrence(
            command_kind=command.command_kind,
            command_body_hash=command.command_body_hash,
            subject="issuer" if is_issue else command.account_owner,
            grant=TOKEN_ROOTS["issue-grant" if is_issue else "burn-grant"],
            nonce=nonce,
        )
        return HistoryStep(label, occurrence_label, _context(occurrence), command)

    issue_alice_twenty = _issue("alice", 20)
    issue_bob_five = _issue("bob", 5)
    burn_bob_five = _burn("bob", 5)
    # The replayed step reuses the identical occurrence, so it carries the
    # identical derived occurrence id.
    replayed = authorized_step("h1_issue_alice", issue_alice_twenty, "occ:h1", 201)
    steps = (
        replayed,
        HistoryStep(
            "h2_issue_alice_replayed_occurrence",
            "occ:h1",
            replayed.context,
            issue_alice_twenty,
        ),
        HistoryStep(
            "h3_issue_rejected_unauthorized",
            "occ:h3",
            _context(
                _occurrence(
                    command_kind=issue_bob_five.command_kind,
                    command_body_hash=issue_bob_five.command_body_hash,
                    subject="mallory",
                    grant=TOKEN_ROOTS["issue-grant"],
                    nonce=203,
                )
            ),
            issue_bob_five,
        ),
        authorized_step("h4_issue_bob", issue_bob_five, "occ:h4", 204),
        HistoryStep(
            "h5_burn_rejected_wrong_presenter",
            "occ:h5",
            _context(
                _occurrence(
                    command_kind=burn_bob_five.command_kind,
                    command_body_hash=burn_bob_five.command_body_hash,
                    subject="alice",
                    grant=TOKEN_ROOTS["burn-grant"],
                    nonce=205,
                )
            ),
            burn_bob_five,
        ),
        authorized_step("h6_burn_bob_all", burn_bob_five, "occ:h6", 206),
        authorized_step("h7_burn_bob_rejected_empty_row", _burn("bob", 1), "occ:h7", 207),
        authorized_step("h8_burn_alice_partial", _burn("alice", 15), "occ:h8", 208),
    )
    return start, steps


TWINS: tuple[Twin, ...] = _build_twins()
TWINS_BY_NAME: dict[str, Twin] = {twin.name: twin for twin in TWINS}
HISTORY_START, HISTORY_STEPS = _build_history()
ALL_NAMES: tuple[str, ...] = tuple(twin.name for twin in TWINS)
ACCEPTED_NAMES: tuple[str, ...] = tuple(
    twin.name
    for twin in TWINS
    if isinstance(
        transition_managed_asset_lifecycle_v2(twin.context, twin.state, twin.command),
        ManagedAssetLifecycleAcceptedV2,
    )
)


# --------------------------------------------------------------------------
# Projections of the live Python result onto the modeled observation set.
# --------------------------------------------------------------------------


def _account_total(state: ManagedAssetLifecycleStateV2, asset: str) -> int:
    return sum(row.amount_atoms for row in state.balances if row.asset == asset)


def _flag(value: bool) -> str:
    return "true" if value else "false"


def _expected_authorization_root(
    policy: ManagedAssetLifecyclePolicyV2, command: ManagedAssetLifecycleCommandV2
) -> str | None:
    if command.command_kind == MANAGED_ASSET_ISSUE_COMMAND_KIND_V2:
        return policy.issue_authorization_root
    return policy.burn_authorization_root


def _python_scenario_fields(twin: Twin) -> tuple[str, ...]:
    policy = twin.state.policies[0]
    command = twin.command
    return (
        twin.name,
        command.command_kind,
        command.asset,
        command.asset_class.value,
        str(command.atom_decimals),
        command.account_owner,
        str(command.amount_atoms),
        policy.asset,
        policy.asset_class.value,
        str(policy.atom_decimals),
        str(twin.state.supply_atoms(policy.asset)),
        str(_account_total(twin.state, policy.asset)),
        *(str(twin.state.balance_atoms(p, policy.asset)) for p in REPORTED_PRINCIPALS),
    )


def _python_relation_fields(twin: Twin) -> tuple[str, ...]:
    """Recompute the guard *inputs* the model reads, never a guard decision."""

    policy = twin.state.policies[0]
    command = twin.command
    occurrence = twin.context.occurrence
    expected = _expected_authorization_root(policy, command)
    is_issue = command.command_kind == MANAGED_ASSET_ISSUE_COMMAND_KIND_V2
    delta_ceiling = MAX_DELTA_ATOMS_V2 if is_issue else -MIN_DELTA_ATOMS_V2

    def with_occurrence(value: object) -> str:
        if occurrence is None:
            return "absent"
        return _flag(bool(value))

    return (
        twin.name,
        _flag(occurrence is not None),
        with_occurrence(
            occurrence is not None
            and occurrence.pre_state_root == twin.context.global_pre_state_root
        ),
        with_occurrence(occurrence is not None and occurrence.consumed_object_ids == ()),
        _flag(twin.context.module_release_id == twin.state.module_release_id),
        with_occurrence(occurrence is not None and occurrence.command_kind == command.command_kind),
        with_occurrence(
            occurrence is not None
            and occurrence.command_body_hash == command.command_body_hash
        ),
        _flag(command.asset == policy.asset),
        _flag(policy.enabled is True),
        _flag(command.asset_class is policy.asset_class),
        _flag(command.atom_decimals == policy.atom_decimals),
        _flag(policy.asset_origin_root is not None and command.asset_origin_root is not None),
        _flag(command.asset_origin_root == policy.asset_origin_root),
        _flag(policy.asset_class is AssetClassV2.REGISTERED_ORDINARY_TOKEN),
        _flag(policy.issue_authorization_root is not None),
        _flag(policy.burn_authorization_root is not None),
        with_occurrence(
            occurrence is not None
            and policy.issue_authority_subject is not None
            and policy.issue_authority_subject == occurrence.subject_id
        ),
        with_occurrence(occurrence is not None and occurrence.subject_id == command.account_owner),
        with_occurrence(
            occurrence is not None and expected is not None and occurrence.grant_root == expected
        ),
        _flag(command.authorization_root == expected),
        _flag(command.amount_atoms != 0),
        _flag(command.amount_atoms <= delta_ceiling),
    )


def _post_state_of(
    result: ManagedAssetLifecycleResultV2, pre: ManagedAssetLifecycleStateV2
) -> ManagedAssetLifecycleStateV2:
    if isinstance(result, ManagedAssetLifecycleAcceptedV2):
        return result.post_state
    return pre


def _python_outcome_fields(
    twin: Twin, result: ManagedAssetLifecycleResultV2, occurrence_id_labels: dict[str, str]
) -> tuple[str, ...]:
    policy = twin.state.policies[0]
    post = _post_state_of(result, twin.state)
    effects = result.effects
    if isinstance(result, ManagedAssetLifecycleAcceptedV2):
        verdict = "ACCEPTED"
        lane_matches = effects.lane_writes == (
            LaneWriteV2(LaneIdV2.ASSET_TRANSFER, twin.state.state_root, post.state_root),
        )
    else:
        verdict = result.code.value
        lane_matches = False
    consumptions = ";".join(
        occurrence_id_labels[identifier] for identifier in effects.occurrence_consumptions
    )
    if isinstance(result, ManagedAssetLifecycleAcceptedV2):
        journal = result.module_journal
        external_roots_zero = (
            journal.private_port_root == ZERO_ROOT_V2
            and journal.terminal_obligations_root == ZERO_ROOT_V2
            and journal.oracle_occurrence_plan_root == ZERO_ROOT_V2
        )
    else:
        external_roots_zero = (
            result.terminal_obligations_root == ZERO_ROOT_V2
            and result.oracle_occurrence_plan_root == ZERO_ROOT_V2
        )
    return (
        twin.name,
        verdict,
        str(post.supply_atoms(policy.asset)),
        str(_account_total(post, policy.asset)),
        str(len(effects.lane_writes)),
        _flag(lane_matches),
        str(len(effects.occurrence_consumptions)),
        consumptions,
        str(len(effects.external_outbox_enqueue)),
        _flag(external_roots_zero),
        _flag(bool(effects.rows)),
        *(str(post.balance_atoms(p, policy.asset)) for p in REPORTED_PRINCIPALS),
    )


def _python_payload_fields(twin: Twin, result: ManagedAssetLifecycleAcceptedV2) -> tuple[str, ...]:
    effects = result.effects
    rows = effects.rows
    assert len(rows) == 2, twin.name
    movement = next(row for row in rows if row.kind is EconomicEffectKindV2.ACCOUNT_MOVEMENT)
    supply_row = next(
        row for row in rows if row.kind is not EconomicEffectKindV2.ACCOUNT_MOVEMENT
    )
    assert len(effects.asset_conservation) == 1, twin.name
    conservation = effects.asset_conservation[0]
    return (
        twin.name,
        movement.principal,
        str(movement.delta_atoms),
        supply_row.kind.value,
        str(supply_row.delta_atoms),
        str(conservation.owned_and_custodied_pre_atoms),
        str(conservation.owned_and_custodied_post_atoms),
        str(conservation.supply_pre_atoms),
        str(conservation.supply_post_atoms),
        str(conservation.authorized_issue_atoms),
        str(conservation.authorized_burn_atoms),
    )


# --------------------------------------------------------------------------
# Lean compilation and report evaluation.
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class CompiledPacket:
    """Everything the later gates need.

    Only the two Lean variables this gate sets are carried; the inherited
    process environment is never stored on, or returned from, a fixture.
    """

    build_root: Path
    lean: Path
    lean_overrides: dict[str, str]
    report: dict[str, list[tuple[str, ...]]]


def _lean_environment(overrides: dict[str, str]) -> dict[str, str]:
    """Inherit the process environment minus any ambient Lean search paths."""

    environment = {
        key: value
        for key, value in os.environ.items()
        if key not in {"LEAN_PATH", "LEAN_SRC_PATH"}
    }
    environment.update(overrides)
    return environment


def _run(
    command: list[str],
    *,
    overrides: dict[str, str] | None = None,
    timeout: int = 600,
) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        command,
        cwd=ROOT,
        env=None if overrides is None else _lean_environment(overrides),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=timeout,
        check=False,
    )


def _parse_report(text: str) -> dict[str, list[tuple[str, ...]]]:
    rows: dict[str, list[tuple[str, ...]]] = {}
    for line in text.splitlines():
        if not line:
            continue
        fields = tuple(line.split(","))
        rows.setdefault(fields[0], []).append(fields[1:])
    return rows


@pytest.fixture(scope="module")
def packet(tmp_path_factory: pytest.TempPathFactory) -> CompiledPacket:
    assert (LEAN_DIR / "lean-toolchain").read_text(encoding="utf-8").strip() == PINNED_TOOLCHAIN
    lean_executable = shutil.which("lean")
    assert lean_executable is not None, "this gate requires the Lean executable"
    lean = Path(lean_executable)

    overrides = {"ELAN_TOOLCHAIN": PINNED_TOOLCHAIN}
    version = _run([str(lean), "--version"], overrides=overrides, timeout=60)
    assert version.returncode == 0, version.stdout + version.stderr
    assert "version 4.27.0" in version.stdout

    build_root = tmp_path_factory.mktemp("managed-asset-runtime-parity-v2")
    (build_root / "Proofs").mkdir()
    overrides["LEAN_PATH"] = str(build_root)
    for target in (ASSET_PROOF, MANAGED_PROOF, PARITY_PROOF):
        output = build_root / "Proofs" / f"{target.stem}.olean"
        result = _run(
            [
                str(lean),
                "-DwarningAsError=true",
                "-R",
                str(LEAN_DIR),
                "-o",
                str(output),
                str(target),
            ],
            overrides=overrides,
        )
        assert result.returncode == 0, result.stdout + result.stderr
        assert result.stdout.strip() == "", target.name
        assert result.stderr.strip() == "", target.name
        assert output.is_file()

    probe = build_root / "RuntimeParityReport.lean"
    probe.write_text(
        f"import {PARITY_NAMESPACE}\n\n"
        f"#eval IO.println {PARITY_NAMESPACE}.runtimeParityReportV2\n",
        encoding="utf-8",
    )
    emitted = _run([str(lean), "-DwarningAsError=true", str(probe)], overrides=overrides)
    assert emitted.returncode == 0, emitted.stdout + emitted.stderr
    assert emitted.stderr.strip() == ""
    return CompiledPacket(build_root, lean, overrides, _parse_report(emitted.stdout))


@pytest.fixture(scope="module")
def occurrence_id_labels() -> dict[str, str]:
    """Map each derived Python occurrence id to the Lean vector's opaque label.

    The map is required to be a bijection, so 'the same occurrence' means the
    same thing on both sides -- which is what makes the replayed history step
    evidence rather than a coincidence.
    """

    labels: dict[str, str] = {}
    for twin in TWINS:
        occurrence = twin.context.occurrence
        if occurrence is None:
            continue
        labels[occurrence.occurrence_id] = twin.occurrence_label
    for step in HISTORY_STEPS:
        occurrence = step.context.occurrence
        assert occurrence is not None
        existing = labels.get(occurrence.occurrence_id)
        assert existing in (None, step.occurrence_label), step.label
        labels[occurrence.occurrence_id] = step.occurrence_label
    assert len(set(labels.values())) == len(labels), "occurrence labels are not injective"
    return labels


# --------------------------------------------------------------------------
# Gate 1: the Lean module itself.
# --------------------------------------------------------------------------


def test_parity_module_compiles_with_pinned_lean_and_warnings_as_errors(
    packet: CompiledPacket,
) -> None:
    assert (packet.build_root / "Proofs" / "ManagedAssetRuntimeParityV2.olean").is_file()


def test_every_theorem_declaration_is_explicitly_tracked() -> None:
    source = PARITY_PROOF.read_text(encoding="utf-8")
    declared = tuple(
        re.findall(
            r"^theorem\s+([A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*)(?=\s|:)",
            source,
            re.MULTILINE,
        )
    )
    assert declared == PARITY_THEOREMS
    assert len(set(PARITY_THEOREMS)) == len(PARITY_THEOREMS)
    assert "import Proofs.ManagedAssetLifecycleRefinementV2" in source


def test_parity_module_has_no_placeholders_or_local_axioms(packet: CompiledPacket) -> None:
    source = PARITY_PROOF.read_text(encoding="utf-8")
    for token in FORBIDDEN_PROOF_TOKENS:
        assert token not in source, token
    assert SCANNER.is_file()
    result = _run([sys.executable, str(SCANNER), str(PARITY_PROOF), "--json"], timeout=120)
    assert result.returncode == 0, result.stdout + result.stderr


def test_every_tracked_theorem_uses_only_standard_axioms(packet: CompiledPacket) -> None:
    qualified = tuple(f"{PARITY_NAMESPACE}.{name}" for name in PARITY_THEOREMS)
    probe = packet.build_root / "ParityAxiomDependencies.lean"
    probe.write_text(
        f"import {PARITY_NAMESPACE}\n\n"
        + "\n".join(f"#print axioms {name}" for name in qualified)
        + "\n",
        encoding="utf-8",
    )
    result = _run(
        [str(packet.lean), "-DwarningAsError=true", str(probe)], overrides=packet.lean_overrides
    )
    assert result.returncode == 0, result.stdout + result.stderr
    dependencies: set[str] = set()
    for body in re.findall(r"depends on axioms:\s*\[([^\]]*)\]", result.stdout, re.DOTALL):
        dependencies.update(item.strip() for item in body.split(",") if item.strip())
    for name in qualified:
        assert f"'{name}'" in result.stdout, name
    assert dependencies <= ALLOWED_STANDARD_AXIOMS


# --------------------------------------------------------------------------
# Gate 2: the two tables describe the same scenarios.
# --------------------------------------------------------------------------


def test_root_token_map_is_injective() -> None:
    assert len(set(TOKEN_ROOTS.values())) == len(TOKEN_ROOTS)


def test_report_declares_the_reject_enum_and_width_constants_the_runtime_uses(
    packet: CompiledPacket,
) -> None:
    codes = [fields[1] for fields in packet.report["CODE"]]
    ranks = [int(fields[0]) for fields in packet.report["CODE"]]
    assert ranks == list(range(len(codes)))
    assert tuple(codes) == tuple(code.value for code in ManagedAssetLifecycleRejectCodeV2)
    (width,) = packet.report["WIDTH"]
    assert width == (str(MAX_ATOMS_V2), str(MIN_DELTA_ATOMS_V2), str(MAX_DELTA_ATOMS_V2))
    (principals,) = packet.report["PRINCIPALS"]
    assert principals == REPORTED_PRINCIPALS


def test_report_covers_exactly_the_python_vector_table(packet: CompiledPacket) -> None:
    reported = [fields[0] for fields in packet.report["SCENARIO"]]
    assert reported == [twin.name for twin in TWINS]
    assert len(reported) == len(set(reported)) == 37


@pytest.mark.parametrize("name", ALL_NAMES)
def test_lean_vector_and_python_twin_describe_the_same_scenario(
    packet: CompiledPacket, name: str
) -> None:
    twin = TWINS_BY_NAME[name]
    (scenario,) = [fields for fields in packet.report["SCENARIO"] if fields[0] == name]
    (relation,) = [fields for fields in packet.report["RELATION"] if fields[0] == name]
    assert scenario == _python_scenario_fields(twin)
    assert relation == _python_relation_fields(twin)


# --------------------------------------------------------------------------
# Gate 3: complete outcome parity.
# --------------------------------------------------------------------------


@pytest.mark.parametrize("name", ALL_NAMES)
def test_complete_outcome_matches_the_model(
    packet: CompiledPacket, occurrence_id_labels: dict[str, str], name: str
) -> None:
    twin = TWINS_BY_NAME[name]
    before_bytes = canonical_global_bytes_v2(twin.state.to_canonical())
    before_root = twin.state.state_root

    result = transition_managed_asset_lifecycle_v2(twin.context, twin.state, twin.command)

    (outcome,) = [fields for fields in packet.report["OUTCOME"] if fields[0] == name]
    assert outcome == _python_outcome_fields(twin, result, occurrence_id_labels)

    assert canonical_global_bytes_v2(twin.state.to_canonical()) == before_bytes
    assert twin.state.state_root == before_root


@pytest.mark.parametrize("name", ALL_NAMES)
def test_rejection_is_an_exact_no_op_and_acceptance_carries_effects(
    packet: CompiledPacket, name: str
) -> None:
    twin = TWINS_BY_NAME[name]
    (outcome,) = [fields for fields in packet.report["OUTCOME"] if fields[0] == name]
    result = transition_managed_asset_lifecycle_v2(twin.context, twin.state, twin.command)
    if outcome[1] == "ACCEPTED":
        assert isinstance(result, ManagedAssetLifecycleAcceptedV2)
        assert not result.effects.is_empty
        assert result.module_journal.pre_lane_root == twin.state.state_root
        assert result.module_journal.post_lane_root == result.post_state.state_root
        return
    assert isinstance(result, ManagedAssetLifecycleRejectedV2)
    assert result.code.value == outcome[1]
    assert result.pre_state_root == twin.state.state_root
    assert result.post_state_root == twin.state.state_root
    assert result.effects.is_empty
    assert result.terminal_obligations_root == ZERO_ROOT_V2
    assert result.oracle_occurrence_plan_root == ZERO_ROOT_V2


@pytest.mark.parametrize("name", ACCEPTED_NAMES)
def test_accepted_effect_payload_matches_the_model(packet: CompiledPacket, name: str) -> None:
    twin = TWINS_BY_NAME[name]
    result = transition_managed_asset_lifecycle_v2(twin.context, twin.state, twin.command)
    assert isinstance(result, ManagedAssetLifecycleAcceptedV2)
    (payload,) = [fields for fields in packet.report["PAYLOAD"] if fields[0] == name]
    assert payload == _python_payload_fields(twin, result)


@pytest.mark.parametrize("name", ALL_NAMES)
def test_runtime_effect_shape_outside_the_modeled_projection(name: str) -> None:
    """Fields the bounded model does not carry, checked directly on the runtime.

    These are runtime contract assertions, not parity: the model says nothing
    about custody domains, fee rows, or the outbox row type.
    """

    twin = TWINS_BY_NAME[name]
    result = transition_managed_asset_lifecycle_v2(twin.context, twin.state, twin.command)
    effects = result.effects
    assert effects.fee_conservation == ()
    assert effects.external_outbox_enqueue == ()
    if not isinstance(result, ManagedAssetLifecycleAcceptedV2):
        assert effects.rows == ()
        assert effects.asset_conservation == ()
        assert effects.lane_writes == ()
        assert effects.occurrence_consumptions == ()
        return
    assert len(effects.rows) == 2
    assert {row.kind for row in effects.rows} == {
        EconomicEffectKindV2.ACCOUNT_MOVEMENT,
        EconomicEffectKindV2.ISSUE
        if twin.command.command_kind == MANAGED_ASSET_ISSUE_COMMAND_KIND_V2
        else EconomicEffectKindV2.BURN,
    }
    for row in effects.rows:
        assert row.custody_domain == ACCOUNT_CUSTODY_DOMAIN_V2
        assert row.asset == twin.command.asset
        assert row.principal == twin.command.account_owner
    assert len(effects.asset_conservation) == 1
    assert effects.asset_conservation[0].asset == twin.command.asset
    journal = result.module_journal
    assert journal.lane_id is LaneIdV2.ASSET_TRANSFER
    assert journal.module_release_id == twin.state.module_release_id
    assert journal.private_port_root == ZERO_ROOT_V2
    assert journal.terminal_obligations_root == ZERO_ROOT_V2
    assert journal.oracle_occurrence_plan_root == ZERO_ROOT_V2


def test_every_reachable_reject_code_is_exercised_by_the_live_runtime(
    packet: CompiledPacket,
) -> None:
    observed = set()
    accepted = 0
    for twin in TWINS:
        result = transition_managed_asset_lifecycle_v2(twin.context, twin.state, twin.command)
        if isinstance(result, ManagedAssetLifecycleRejectedV2):
            observed.add(result.code)
        else:
            accepted += 1
    unreachable = {
        ManagedAssetLifecycleRejectCodeV2.ASSET_DECIMALS_MISMATCH,
        ManagedAssetLifecycleRejectCodeV2.BALANCE_OVERFLOW,
    }
    assert observed == set(ManagedAssetLifecycleRejectCodeV2) - unreachable
    assert accepted == 10


def test_the_two_unreachable_codes_are_blocked_by_construction_not_by_omission() -> None:
    """`ASSET_DECIMALS_MISMATCH` and `BALANCE_OVERFLOW` are absent from the
    corpus because the typed constructors exclude them, not because the corpus
    is thin.  Both facts are shown here rather than asserted in prose."""

    with pytest.raises(ValueError, match="decimals must equal 8"):
        ManagedAssetLifecycleCommandV2(
            command_kind=MANAGED_ASSET_ISSUE_COMMAND_KIND_V2,
            asset=MODELED_ASSET,
            asset_class=AssetClassV2.REGISTERED_ORDINARY_TOKEN,
            asset_origin_root=TOKEN_ROOTS["origin-ord"],
            atom_decimals=7,
            authorization_root=TOKEN_ROOTS["issue-grant"],
            account_owner="alice",
            amount_atoms=1,
        )
    with pytest.raises(ValueError, match="balances exceed supply"):
        _state(_policy(), (("alice", 11),), 10)


# --------------------------------------------------------------------------
# Gate 4: the fixed semantic mutants.
# --------------------------------------------------------------------------


def test_fixed_semantic_mutants_are_killed_by_the_live_runtime(
    packet: CompiledPacket,
) -> None:
    """Each mutant changes one clause of the model.  The runtime agrees with the
    real model and disagrees with the mutant on the named vector, so the corpus
    discriminates that clause.  This bounds corpus weakness for these three
    clauses only; it is not a general mutation score."""

    rows = {fields[0]: fields for fields in packet.report["MUTANT"]}
    killed: list[tuple[str, str]] = []
    for name, mutant_index, mutant_id in (
        ("issue_supply_and_balance_would_both_overflow", 2, "M1"),
        ("burn_by_account_owner", 3, "M2"),
    ):
        twin = TWINS_BY_NAME[name]
        result = transition_managed_asset_lifecycle_v2(twin.context, twin.state, twin.command)
        runtime = (
            "ACCEPTED"
            if isinstance(result, ManagedAssetLifecycleAcceptedV2)
            else result.code.value
        )
        real, mutant = rows[name][1], rows[name][mutant_index]
        assert runtime == real, (mutant_id, name)
        assert runtime != mutant, (mutant_id, name)
        killed.append((mutant_id, mutant))
    assert killed == [
        ("M1", "BALANCE_OVERFLOW"),
        ("M2", "UNAUTHORIZED_SUBJECT"),
    ]

    # M3 changes the reported post supply in the conservation row.
    name = "issue_to_existing_holder"
    twin = TWINS_BY_NAME[name]
    result = transition_managed_asset_lifecycle_v2(twin.context, twin.state, twin.command)
    assert isinstance(result, ManagedAssetLifecycleAcceptedV2)
    (mutated,) = [fields for fields in packet.report["MUTANT_M3"] if fields[0] == name]
    (payload,) = [fields for fields in packet.report["PAYLOAD"] if fields[0] == name]
    runtime_supply_post = str(result.effects.asset_conservation[0].supply_post_atoms)
    assert runtime_supply_post == payload[8]
    assert runtime_supply_post != mutated[1]


def test_every_mutant_row_agrees_with_the_live_runtime_outside_its_divergence_set(
    packet: CompiledPacket,
) -> None:
    m1_divergent = {"issue_supply_and_balance_would_both_overflow"}
    m2_divergent = {
        "burn_by_account_owner",
        "burn_removes_row_at_exact_balance",
        "burn_at_negated_i128_min_delta",
        "burn_presented_by_policy_issuer_not_owner",
        "burn_delta_overflow_at_i128_min_neighbor",
        "burn_exceeds_supply",
        "burn_exceeds_owner_balance_with_supply_available",
    }
    observed_m1: set[str] = set()
    observed_m2: set[str] = set()
    for fields in packet.report["MUTANT"]:
        name, real, mutant_m1, mutant_m2 = fields
        twin = TWINS_BY_NAME[name]
        result = transition_managed_asset_lifecycle_v2(twin.context, twin.state, twin.command)
        runtime = (
            "ACCEPTED"
            if isinstance(result, ManagedAssetLifecycleAcceptedV2)
            else result.code.value
        )
        assert runtime == real, name
        if mutant_m1 != runtime:
            observed_m1.add(name)
        if mutant_m2 != runtime:
            observed_m2.add(name)
    assert observed_m1 == m1_divergent
    assert observed_m2 == m2_divergent


# --------------------------------------------------------------------------
# Gate 5: stateful history, rejected no-change steps, and occurrence replay.
# --------------------------------------------------------------------------


def test_stateful_history_matches_the_model_step_by_step(
    packet: CompiledPacket, occurrence_id_labels: dict[str, str]
) -> None:
    policy_asset = MODELED_ASSET
    (start,) = packet.report["HISTORY_START"]
    assert start == (
        str(HISTORY_START.supply_atoms(policy_asset)),
        str(_account_total(HISTORY_START, policy_asset)),
        *(str(HISTORY_START.balance_atoms(p, policy_asset)) for p in REPORTED_PRINCIPALS),
    )

    rows = packet.report["HISTORY"]
    assert [fields[0] for fields in rows] == [step.label for step in HISTORY_STEPS]

    state = HISTORY_START
    rejected_steps = 0
    for step, fields in zip(HISTORY_STEPS, rows, strict=True):
        before_bytes = canonical_global_bytes_v2(state.to_canonical())
        before_root = state.state_root
        result = transition_managed_asset_lifecycle_v2(step.context, state, step.command)
        post = _post_state_of(result, state)
        if isinstance(result, ManagedAssetLifecycleRejectedV2):
            rejected_steps += 1
            verdict = result.code.value
            # A rejected step must not move the history forward at all.
            assert result.pre_state_root == before_root
            assert result.post_state_root == before_root
            assert post is state
            assert canonical_global_bytes_v2(post.to_canonical()) == before_bytes
        else:
            assert isinstance(result, ManagedAssetLifecycleAcceptedV2)
            verdict = "ACCEPTED"
        consumptions = ";".join(
            occurrence_id_labels[identifier]
            for identifier in result.effects.occurrence_consumptions
        )
        assert fields == (
            step.label,
            step.command.command_kind,
            step.command.account_owner,
            str(step.command.amount_atoms),
            verdict,
            str(post.supply_atoms(policy_asset)),
            str(_account_total(post, policy_asset)),
            str(len(result.effects.occurrence_consumptions)),
            consumptions,
            _flag(
                post.supply_atoms(policy_asset) == state.supply_atoms(policy_asset)
                and _account_total(post, policy_asset) == _account_total(state, policy_asset)
            ),
            *(str(post.balance_atoms(p, policy_asset)) for p in REPORTED_PRINCIPALS),
        )
        state = post
    assert rejected_steps == 3


def test_the_leaf_has_no_replay_guard_and_the_model_records_the_same_gap(
    packet: CompiledPacket,
) -> None:
    """Observation, not a safety claim.

    Steps `h1` and `h2` present the identical occurrence, so they consume the
    identical derived occurrence id.  The leaf accepts both and mints twice.
    Replay defence therefore does not live in this transition; this test pins
    that as a fact about the leaf so a future replay guard has to update it.
    Nothing here says replay is handled by any surrounding component.
    """

    first, second = HISTORY_STEPS[0], HISTORY_STEPS[1]
    first_occurrence = first.context.occurrence
    second_occurrence = second.context.occurrence
    assert first_occurrence is not None and second_occurrence is not None
    assert first_occurrence.occurrence_id == second_occurrence.occurrence_id

    state = HISTORY_START
    accepted: list[ManagedAssetLifecycleAcceptedV2] = []
    for step in (first, second):
        result = transition_managed_asset_lifecycle_v2(step.context, state, step.command)
        assert isinstance(result, ManagedAssetLifecycleAcceptedV2), step.label
        assert result.effects.occurrence_consumptions == (first_occurrence.occurrence_id,)
        accepted.append(result)
        state = result.post_state
    assert state.supply_atoms(MODELED_ASSET) == 40
    assert accepted[0].post_state.state_root != accepted[1].post_state.state_root

    rows = {fields[0]: fields for fields in packet.report["HISTORY"]}
    assert rows[first.label][4] == "ACCEPTED"
    assert rows[second.label][4] == "ACCEPTED"
    assert rows[first.label][8] == rows[second.label][8] == "occ:h1"


# --------------------------------------------------------------------------
# Gate 6: the scope statement is carried in the sources, not only here.
# --------------------------------------------------------------------------


def test_parity_module_states_its_abstractions_and_non_claims() -> None:
    source = " ".join(PARITY_PROOF.read_text(encoding="utf-8").split())
    for phrase in (
        "opaque equality tokens",
        "no hash, digest, or codec equivalence is claimed",
        "bounded differential over a finite enumerated corpus",
        "It is not a refinement proof of the Python source",
        "does not upgrade any production claim",
    ):
        assert phrase in source, phrase
