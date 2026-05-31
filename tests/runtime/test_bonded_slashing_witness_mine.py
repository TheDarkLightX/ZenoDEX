"""Symbolic disaster-witness mine for ZenoLedger BONDED SLASHING receipts.

`apply_bonded_slashing_v0` is the consensus-critical transition that turns a
*proven equivocation evidence packet* + a *bond registry* + a *bounded slashing
policy* into a single slashing receipt (slash / burn / treasury split) and a new
bond registry. It is the value-affecting authority path: it decides HOW MUCH of a
validator's / watcher's bond is destroyed.

Disaster class mined here (OVER-SLASH / UNDER-SLASH / phantom slash):

  On any ADMIT (a receipt produced without raising):

    INV-1 (no over-slash):     0 < slash_amount <= bonded - already_slashed
                               and remaining_bond == bonded - already_slashed - slash_amount >= 0
                               and new slashed_amount (= already_slashed + slash_amount) <= bonded
    INV-2 (split conservation): burn_amount + treasury_amount == slash_amount,
                               burn_amount >= 0, treasury_amount >= 0
    INV-3 (policy bounds):     slash_amount <= policy.max_slash_amount and
                               slash_amount >= min(policy.min_slash_amount, available)-aware lower
                               bound — concretely slash_amount >= policy.min_slash_amount
                               whenever min <= available (build guarantees min <= max).
    INV-4 (no phantom slash):  the receipt's (subject_id, subject_kind) names a
                               registry entry that was ACTIVE and bonded, and the
                               evidence height was inside its slashability window;
                               the updated registry mutates ONLY that subject's
                               (slashed_amount, status, processed_evidence_hashes)
                               and conserves every other entry verbatim.
    INV-5 (determinism):       identical inputs -> identical receipt_hash and
                               bond_registry_hash_after.

  And the reject-is-no-op property: a malformed policy / evidence / registry that
  raises must NOT have mutated the caller's inputs (the transition takes Mappings
  by value via dict(...), so we additionally assert the input objects are
  unchanged).

SCOPE / NON-CLAIMS:
  * This module performs NO BLS/signature verification — it binds by canonical
    re-hash (hash_v0) of evidence/policy/registry bodies. There is therefore NO
    crypto oracle to stub here (crypto_oracle_stubbed = false). Aggregate /
    signature forgery is OUT of scope and asserted nowhere.
  * Evidence equivocation *soundness* (that two checkpoints genuinely conflict)
    is owned by `zeno_ledger_anti_equivocation_v0` and is only used here as a
    valid-input builder; we do not re-derive it.
  * Cross-module sequencing (multiple slashes in a chain, registry persistence,
    epoch transitions) is NOT covered — single-transition only.
  * We mine ONLY the checkpoint_equivocation evidence kind (cheapest valid
    builder); the watcher kind shares the same slash math and is exercised by the
    example suite.
"""

from __future__ import annotations

import copy

import pytest

hypothesis = pytest.importorskip("hypothesis")
from hypothesis import HealthCheck, given, settings  # noqa: E402
from hypothesis import strategies as st  # noqa: E402

from src.integration import zeno_ledger_bonded_slashing_v0 as m  # noqa: E402
from src.integration.zeno_ledger_anti_equivocation_v0 import (  # noqa: E402
    build_checkpoint_equivocation_slashing_evidence_v0,
)
from src.integration.zeno_ledger_v0 import build_checkpoint_v0, build_header_v0, hash_v0  # noqa: E402

BPS = m.BPS_SCALE_V0
ZERO_ROOT = "0x" + "00" * 32
CHAIN_ID = "zeno-ledger-slashing-mine-0"


def _root(label: str) -> str:
    return hash_v0("bonded_slashing_mine_root", {"label": label})


def _header(*, height: int, body_label: str) -> dict[str, object]:
    return build_header_v0(
        chain_id=CHAIN_ID,
        height=height,
        time_ms=1_778_730_000_000 + height,
        prev_header_hash=ZERO_ROOT,
        sequencer_set_hash=_root("validator-set"),
        ingress_root=_root(f"ingress-{body_label}"),
        tx_root=_root(f"tx-{body_label}"),
        pre_state_root=_root(f"pre-{body_label}"),
        post_state_root=_root(f"post-{body_label}"),
        app_hash=_root(f"app-{body_label}"),
        evidence_root=_root(f"evidence-{body_label}"),
        body_root=_root(f"body-{body_label}"),
        data_availability_root=_root(f"da-{body_label}"),
        proof_journal_hash=_root(f"proof-{body_label}"),
        config_digest=_root("config"),
        module_versions_digest=_root("modules"),
        signature_set_root=ZERO_ROOT,
    )


def _checkpoint_evidence(*, height: int, label_a: str, label_b: str) -> dict[str, object]:
    checkpoint_a = build_checkpoint_v0(_header(height=height, body_label=label_a))
    checkpoint_b = build_checkpoint_v0(_header(height=height, body_label=label_b))
    return build_checkpoint_equivocation_slashing_evidence_v0(checkpoint_a, checkpoint_b)


# ---------------------------------------------------------------------------
# Invariant helper — factored out so the TEETH test can reuse it verbatim.
# ---------------------------------------------------------------------------
def _assert_no_overslash(
    *,
    receipt: dict,
    updated_registry: dict,
    registry_before: dict,
    policy: dict,
    subject_id: str,
    subject_kind: str,
    evidence_height: int,
) -> None:
    """Encode the OVER/UNDER/phantom-slash safety contract on a produced receipt.

    Raises AssertionError on any violation: a slash above the available bond, a
    negative remaining bond, a broken burn/treasury split, a policy-cap breach, a
    phantom subject, or a registry mutation that touches a non-subject entry."""

    # --- locate the bond entry that was the slashing subject (must exist & be
    #     active, inside window) — INV-4 anchor ---
    before_entry = None
    for entry in registry_before["entries"]:
        if entry["subject_id"] == subject_id and entry["subject_kind"] == subject_kind:
            before_entry = entry
            break
    assert before_entry is not None, (
        f"PHANTOM SLASH: receipt slashed ({subject_id!r},{subject_kind!r}) "
        f"with no matching bonded entry"
    )
    assert before_entry["status"] == "active", (
        f"PHANTOM SLASH: receipt slashed a non-active bond (status="
        f"{before_entry['status']!r})"
    )
    assert evidence_height <= int(before_entry["slashable_until_height"]), (
        f"PHANTOM SLASH: evidence_height {evidence_height} outside slashability "
        f"window {before_entry['slashable_until_height']}"
    )

    bonded = int(before_entry["bonded_amount"])
    already = int(before_entry["slashed_amount"])
    available = bonded - already
    slash = int(receipt["slash_amount"])
    burn = int(receipt["burn_amount"])
    treasury = int(receipt["treasury_amount"])
    remaining = int(receipt["remaining_bond"])

    # --- INV-1: no over-slash ---
    assert slash > 0, f"zero/negative slash admitted: {slash}"
    assert slash <= available, (
        f"OVER-SLASH: slash {slash} > available bond {available} "
        f"(bonded={bonded}, already_slashed={already})"
    )
    assert remaining == available - slash, (
        f"remaining_bond {remaining} != available-slash {available - slash}"
    )
    assert remaining >= 0, f"OVER-SLASH: negative remaining bond {remaining}"
    assert already + slash <= bonded, (
        f"OVER-SLASH: cumulative slashed {already + slash} exceeds bond {bonded}"
    )

    # --- receipt's own accounting must agree with the registry it claims to read ---
    assert int(receipt["bonded_amount_before"]) == bonded
    assert int(receipt["already_slashed_before"]) == already

    # --- INV-2: split conservation ---
    assert burn >= 0 and treasury >= 0, f"negative split (burn={burn},treasury={treasury})"
    assert burn + treasury == slash, (
        f"SPLIT LEAK: burn {burn} + treasury {treasury} != slash {slash}"
    )
    # burn split must respect the policy's burn fraction exactly (floor)
    expected_burn = (slash * int(policy["burn_fraction_bps"])) // BPS
    assert burn == expected_burn, f"burn {burn} != floor(slash*burn_bps) {expected_burn}"

    # --- INV-3: policy bounds (build guarantees min <= max) ---
    assert slash <= int(policy["max_slash_amount"]), (
        f"POLICY BREACH: slash {slash} > max_slash_amount {policy['max_slash_amount']}"
    )
    min_slash = int(policy["min_slash_amount"])
    if min_slash <= available:
        assert slash >= min_slash, (
            f"UNDER-SLASH: slash {slash} < policy min_slash_amount {min_slash} "
            f"(available={available})"
        )

    # --- INV-4: updated registry mutates ONLY the subject entry ---
    before_by_id = {e["subject_id"]: e for e in registry_before["entries"]}
    after_by_id = {e["subject_id"]: e for e in updated_registry["entries"]}
    assert set(before_by_id) == set(after_by_id), "registry changed its entry set"
    for sid, after_e in after_by_id.items():
        before_e = before_by_id[sid]
        if sid == subject_id:
            assert int(after_e["slashed_amount"]) == already + slash, (
                f"subject slashed_amount {after_e['slashed_amount']} != {already + slash}"
            )
            assert int(after_e["bonded_amount"]) == bonded, "bonded_amount mutated"
            expected_status = "slashed" if remaining == 0 else "active"
            assert after_e["status"] == expected_status, (
                f"subject status {after_e['status']!r} != {expected_status!r}"
            )
            assert receipt["evidence_hash"] in after_e["processed_evidence_hashes"], (
                "evidence_hash not recorded as processed -> replay possible"
            )
        else:
            # every NON-subject entry must be byte-for-byte conserved
            assert dict(after_e) == dict(before_e), (
                f"COLLATERAL SLASH: non-subject entry {sid!r} mutated: "
                f"{dict(before_e)} -> {dict(after_e)}"
            )


# ---------------------------------------------------------------------------
# TEETH / non-vacuity: plant violations and prove the checker RAISES.
# ---------------------------------------------------------------------------
def test_invariant_catches_planted_violations():
    """If these forged receipts slipped past the helper, every negative receipt
    below would be a FALSE receipt. Each branch plants exactly one disaster."""
    registry_before = {
        "entries": [
            {"subject_id": "s0", "subject_kind": "validator_set", "bonded_amount": 1000,
             "slashed_amount": 0, "slashable_until_height": 100, "status": "active",
             "processed_evidence_hashes": []},
            {"subject_id": "s1", "subject_kind": "validator_set", "bonded_amount": 500,
             "slashed_amount": 0, "slashable_until_height": 100, "status": "active",
             "processed_evidence_hashes": []},
        ]
    }
    policy = {"max_slash_amount": 200, "min_slash_amount": 1, "burn_fraction_bps": 5000}

    def good_after(slash):
        after = copy.deepcopy(registry_before)
        after["entries"][0]["slashed_amount"] = slash
        after["entries"][0]["status"] = "active"
        after["entries"][0]["processed_evidence_hashes"] = ["0x" + "ab" * 32]
        return after

    # (a) OVER-SLASH: slash beyond available bond.
    over = {"slash_amount": 5000, "burn_amount": 2500, "treasury_amount": 2500,
            "remaining_bond": 1000 - 5000, "bonded_amount_before": 1000,
            "already_slashed_before": 0, "evidence_hash": "0x" + "ab" * 32}
    with pytest.raises(AssertionError, match="OVER-SLASH"):
        _assert_no_overslash(receipt=over, updated_registry=good_after(5000),
                             registry_before=registry_before, policy=policy,
                             subject_id="s0", subject_kind="validator_set",
                             evidence_height=7)

    # (b) SPLIT LEAK: burn + treasury != slash.
    leak = {"slash_amount": 100, "burn_amount": 50, "treasury_amount": 60,
            "remaining_bond": 900, "bonded_amount_before": 1000,
            "already_slashed_before": 0, "evidence_hash": "0x" + "ab" * 32}
    with pytest.raises(AssertionError, match="SPLIT LEAK"):
        _assert_no_overslash(receipt=leak, updated_registry=good_after(100),
                             registry_before=registry_before, policy=policy,
                             subject_id="s0", subject_kind="validator_set",
                             evidence_height=7)

    # (c) PHANTOM SLASH: subject not in registry.
    phantom = {"slash_amount": 100, "burn_amount": 50, "treasury_amount": 50,
               "remaining_bond": 900, "bonded_amount_before": 1000,
               "already_slashed_before": 0, "evidence_hash": "0x" + "ab" * 32}
    with pytest.raises(AssertionError, match="PHANTOM SLASH"):
        _assert_no_overslash(receipt=phantom, updated_registry=good_after(100),
                             registry_before=registry_before, policy=policy,
                             subject_id="ghost", subject_kind="validator_set",
                             evidence_height=7)

    # (d) POLICY BREACH: slash above max cap.
    breach = {"slash_amount": 300, "burn_amount": 150, "treasury_amount": 150,
              "remaining_bond": 700, "bonded_amount_before": 1000,
              "already_slashed_before": 0, "evidence_hash": "0x" + "ab" * 32}
    with pytest.raises(AssertionError, match="POLICY BREACH"):
        _assert_no_overslash(receipt=breach, updated_registry=good_after(300),
                             registry_before=registry_before, policy=policy,
                             subject_id="s0", subject_kind="validator_set",
                             evidence_height=7)

    # (e) COLLATERAL SLASH: a non-subject entry mutated.
    collateral_after = good_after(100)
    collateral_after["entries"][1]["slashed_amount"] = 99  # mutate the innocent bond
    valid = {"slash_amount": 100, "burn_amount": 50, "treasury_amount": 50,
             "remaining_bond": 900, "bonded_amount_before": 1000,
             "already_slashed_before": 0, "evidence_hash": "0x" + "ab" * 32}
    with pytest.raises(AssertionError, match="COLLATERAL SLASH"):
        _assert_no_overslash(receipt=valid, updated_registry=collateral_after,
                             registry_before=registry_before, policy=policy,
                             subject_id="s0", subject_kind="validator_set",
                             evidence_height=7)

    # (f) UNDER-SLASH: slash below the policy minimum while it is affordable.
    high_min_policy = {"max_slash_amount": 800, "min_slash_amount": 200,
                       "burn_fraction_bps": 5000}
    under = {"slash_amount": 100, "burn_amount": 50, "treasury_amount": 50,
             "remaining_bond": 900, "bonded_amount_before": 1000,
             "already_slashed_before": 0, "evidence_hash": "0x" + "ab" * 32}
    with pytest.raises(AssertionError, match="UNDER-SLASH"):
        _assert_no_overslash(receipt=under, updated_registry=good_after(100),
                             registry_before=registry_before, policy=high_min_policy,
                             subject_id="s0", subject_kind="validator_set",
                             evidence_height=7)


# ---------------------------------------------------------------------------
# The mine: build VALID evidence/registry/policy, then assert no over/under/
# phantom-slash witness on any ADMIT.
# ---------------------------------------------------------------------------
@settings(max_examples=900, suppress_health_check=[HealthCheck.too_slow])
@given(
    height=st.integers(min_value=0, max_value=20),
    window=st.integers(min_value=0, max_value=20),
    bonded=st.integers(min_value=1, max_value=2000),
    already=st.integers(min_value=0, max_value=2000),
    decoy_bonded=st.integers(min_value=1, max_value=2000),
    slash_frac_bps=st.integers(min_value=0, max_value=BPS),
    min_slash=st.integers(min_value=0, max_value=3000),
    max_slash=st.integers(min_value=1, max_value=3000),
    burn_bps=st.integers(min_value=0, max_value=BPS),
    status=st.sampled_from(["active", "slashed", "revoked"]),
    policy_status=st.sampled_from(["active", "revoked"]),
)
def test_bonded_slashing_has_no_overslash_witness(
    height,
    window,
    bonded,
    already,
    decoy_bonded,
    slash_frac_bps,
    min_slash,
    max_slash,
    burn_bps,
    status,
    policy_status,
):
    if already > bonded:  # build rejects slashed > bonded
        return
    if min_slash > max_slash:  # build rejects min > max
        return

    evidence = _checkpoint_evidence(height=height, label_a="a", label_b="b")
    subject_id = str(evidence["subject_id"])

    # A second, NON-subject "decoy" bond that must never be touched (collateral
    # check). Its subject_id is a distinct canonical 32-byte root.
    decoy_id = _root("decoy-subject")

    registry = m.build_bond_registry_v0(
        chain_id=CHAIN_ID,
        asset_id="ZENO",
        entries=[
            {
                "subject_id": subject_id,
                "subject_kind": "validator_set",
                "bonded_amount": bonded,
                "slashed_amount": already,
                "slashable_until_height": window,
                "status": status,
                "processed_evidence_hashes": [],
            },
            {
                "subject_id": decoy_id,
                "subject_kind": "validator_set",
                "bonded_amount": decoy_bonded,
                "slashed_amount": 0,
                "slashable_until_height": window,
                "status": "active",
                "processed_evidence_hashes": [],
            },
        ],
    )

    try:
        policy = m.build_slashing_policy_v0(
            chain_id=CHAIN_ID,
            policy_id="slashing-policy-mine",
            evidence_kind=str(evidence["evidence_kind"]),
            slash_fraction_bps=slash_frac_bps,
            min_slash_amount=min_slash,
            max_slash_amount=max_slash,
            burn_fraction_bps=burn_bps,
            status=policy_status,
        )
    except ValueError:
        return  # unsatisfiable policy -> nothing to mine

    registry_snapshot = copy.deepcopy(registry)
    policy_snapshot = copy.deepcopy(policy)

    try:
        out = m.apply_bonded_slashing_v0(
            evidence=evidence, bond_registry=registry, policy=policy
        )
    except (ValueError, TypeError):
        # REJECT path: reject-is-no-op — the caller's inputs are unchanged.
        assert registry == registry_snapshot, "reject mutated bond_registry input"
        assert policy == policy_snapshot, "reject mutated policy input"
        return

    receipt = out["receipt"]
    updated_registry = out["bond_registry"]

    # ADMIT: the over/under/phantom-slash contract must hold.
    _assert_no_overslash(
        receipt=receipt,
        updated_registry=updated_registry,
        registry_before=registry,
        policy=policy,
        subject_id=str(receipt["subject_id"]),
        subject_kind=str(receipt["subject_kind"]),
        evidence_height=int(receipt["evidence_height"]),
    )

    # the receipt must bind to the subject named by the EVIDENCE, never a decoy.
    assert receipt["subject_id"] == subject_id, "receipt slashed the wrong subject"

    # reject-is-no-op also holds on the accept path: inputs are taken by value.
    assert registry == registry_snapshot, "accept mutated caller's bond_registry input"
    assert policy == policy_snapshot, "accept mutated caller's policy input"

    # INV-5: determinism — identical inputs reproduce the same receipt + roots.
    out2 = m.apply_bonded_slashing_v0(
        evidence=copy.deepcopy(evidence),
        bond_registry=copy.deepcopy(registry_snapshot),
        policy=copy.deepcopy(policy_snapshot),
    )
    assert out2["receipt"]["receipt_hash"] == receipt["receipt_hash"], "non-deterministic receipt_hash"
    assert out2["receipt"]["bond_registry_hash_after"] == receipt["bond_registry_hash_after"], (
        "non-deterministic bond_registry_hash_after"
    )

    # the receipt's claimed post-root must equal the updated registry's own root.
    assert receipt["bond_registry_hash_after"] == updated_registry["bond_registry_hash"], (
        "receipt post-root does not bind the returned registry"
    )


def test_admit_path_is_reachable():
    """Boundary / non-vacuity for the mine itself: prove a clean ADMIT exists with
    the generated shapes, so the property test is not silently all-reject."""
    evidence = _checkpoint_evidence(height=5, label_a="a", label_b="b")
    registry = m.build_bond_registry_v0(
        chain_id=CHAIN_ID,
        asset_id="ZENO",
        entries=[
            {
                "subject_id": evidence["subject_id"],
                "subject_kind": "validator_set",
                "bonded_amount": 1000,
                "slashed_amount": 0,
                "slashable_until_height": 100,
                "status": "active",
                "processed_evidence_hashes": [],
            }
        ],
    )
    policy = m.build_slashing_policy_v0(
        chain_id=CHAIN_ID,
        policy_id="p",
        evidence_kind=str(evidence["evidence_kind"]),
        slash_fraction_bps=1_000,
        min_slash_amount=1,
        max_slash_amount=200,
        burn_fraction_bps=5_000,
    )
    out = m.apply_bonded_slashing_v0(evidence=evidence, bond_registry=registry, policy=policy)
    assert out["receipt"]["ok"] is True
    assert out["receipt"]["slash_amount"] == 100  # floor(1000 * 0.1)
