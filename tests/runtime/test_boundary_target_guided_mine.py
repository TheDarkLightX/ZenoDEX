"""RUNG-2 boundary / target-guided disaster mine for three ZenoLedger surfaces.

This is a deliberate climb of the input-generation ladder. The committed rung-1
mines (`test_signer_quorum_counting_witness_mine.py`,
`test_bonded_slashing_witness_mine.py`,
`test_ledger_schedule_conflict_witness_mine.py`) draw inputs UNIFORMLY at random.
Uniform sampling spends almost all of its budget in the open interior of each
domain and only rarely lands on the exact knife-edges where off-by-one and
rounding bugs live: `weight == threshold`, `weight == threshold - 1`,
`slash == available`, `burn split residue maximal`, and `height` at the cycle
wrap (`offset % cycle_len == cycle_len - 1` and `== 0`).

TECHNIQUE (the whole point of this file):
  1. `hypothesis.target()` — every example reports a fitness scalar that is
     MAXIMISED when the example sits ON the boundary the disaster class needs.
     The hypothesis engine then steers the search toward those rare states
     (e.g. minimise `abs(accepted_weight - threshold)` => cluster at the quorum
     knife-edge; maximise the split residue `(slash*burn_bps) % BPS`; minimise
     `abs(slash - available)` => slash exactly equal to the available bond;
     minimise distance of `offset % cycle_len` to a wrap boundary).
  2. DISTRIBUTION SHAPING — scalar amounts are drawn from `_boundary_int(...)`,
     an `st.one_of` that lists the boundary anchors (0, 1, 2, max-1, max,
     threshold-1, threshold, threshold+1) MANY times so they are massively
     over-represented relative to a single `st.integers(...)` branch. This makes
     `weight == threshold` (etc.) a *common* event instead of a measure-zero one.

The SAFETY INVARIANTS asserted are identical to the rung-1 mines — quorum
forgery, slash over/under/split-leak/phantom, schedule unfairness — re-asserted
here at the boundary. Each surface keeps its rung-1 teeth test (a planted buggy
reference) so the negative receipt is provably non-vacuous.

A clean run is a bounded NEGATIVE receipt FOR THE BOUNDARY REGION specifically.
A real ADMIT that violates an invariant is a CRITICAL witness (quorum forgery /
slash leak / unfair schedule) to REPORT, not to patch.

SCOPE / NON-CLAIMS (honest):
  * NOT exhaustive: the integer domains (weights, bonds, heights) are unbounded
    in principle; this over-samples the boundary anchors and uses target() to
    cluster there, but does not enumerate a full bounded product.
  * NOT stateful: every example is a single transition. No RuleBasedStateMachine,
    no multi-slash / multi-epoch sequencing.
  * Crypto is out of scope for the quorum surface exactly as in rung-1: the BLS
    envelope check is stubbed to a valid-signature ORACLE so only the COUNTING /
    dedup / threshold logic is exercised. The slashing surface binds by canonical
    re-hash and needs no oracle. The schedule surface uses no signatures.
"""

from __future__ import annotations

import copy

import pytest

hypothesis = pytest.importorskip("hypothesis")
from hypothesis import HealthCheck, given, settings, target  # noqa: E402
from hypothesis import strategies as st  # noqa: E402

from src.integration import zeno_ledger_bonded_slashing_v0 as slash_mod  # noqa: E402
from src.integration import zeno_ledger_signer_registry as reg  # noqa: E402
from src.integration import zeno_ledger_validator_schedule_v0 as vs  # noqa: E402
from src.integration.zeno_ledger_anti_equivocation_v0 import (  # noqa: E402
    build_checkpoint_equivocation_slashing_evidence_v0,
)
from src.integration.zeno_ledger_v0 import (  # noqa: E402
    build_checkpoint_v0,
    build_header_v0,
    hash_v0,
)

PK = lambda i: "0x" + f"{i:096x}"  # noqa: E731  canonical lowercase 48-byte hex
BLS_ALG = reg.SIGNED_ARTIFACT_ALGORITHM_BLS12_381_G2_BASIC_V0
BPS = slash_mod.BPS_SCALE_V0
ZERO_ROOT = "0x" + "00" * 32
CHAIN_ID = "zeno-ledger-boundary-mine-0"
PAYLOAD_KIND = "checkpoint"
PAYLOAD_HASH = "0x" + "ab" * 32


# ---------------------------------------------------------------------------
# Distribution-shaping primitive: a boundary-weighted integer strategy.
# `anchors` are listed once each but appended `weight` extra copies via repeated
# `st.just(...)` branches, so anchors are sampled far more often than the single
# uniform fallback branch. This is the rung-2 difference: boundary values are the
# COMMON case, not measure-zero.
# ---------------------------------------------------------------------------
def _boundary_int(lo: int, hi: int, anchors: list[int], *, repeat: int = 4):
    pool = [a for a in anchors if lo <= a <= hi]
    branches = []
    for a in pool:
        branches.extend([st.just(a)] * repeat)  # over-sample each anchor
    branches.append(st.integers(min_value=lo, max_value=hi))  # uniform fallback
    return st.one_of(*branches)


# ===========================================================================
# A. SIGNATURE QUORUM — knife-edge: accepted_weight vs threshold
# ===========================================================================
@pytest.fixture()
def _bls_oracle(monkeypatch):
    monkeypatch.setattr(reg, "validate_bls_signed_artifact_envelope_v0", lambda **_kw: None)


def _assert_no_forgery(report, *, threshold, active_ids, weight_by_id):
    """Quorum-forgery invariant (identical contract to rung-1)."""
    accepted = report["accepted_signatures"]
    ids = [(s["signer_id"], s["key_id"]) for s in accepted]
    assert len(ids) == len(set(ids)), f"double-counted signer in admit: {ids}"
    for ident in ids:
        assert ident in active_ids, f"admit counted non-active/unregistered {ident}"
    expect_w = sum(weight_by_id[i] for i in ids)
    assert report["accepted_weight"] == expect_w, (
        f"weight mismatch: report={report['accepted_weight']} recomputed={expect_w}"
    )
    assert report["accepted_weight"] >= threshold, (
        f"QUORUM FORGERY: admit at weight {report['accepted_weight']} < threshold {threshold}"
    )


def test_quorum_teeth_catches_forged_certificate():
    """Teeth / non-vacuity (same plant as rung-1): a sub-threshold report and a
    phantom-signer report MUST trip the checker."""
    active_ids = {("signer-0", "key-0")}
    weight_by_id = {("signer-0", "key-0"): 2, ("ghost", "ghost-key"): 9}
    forged_under_threshold = {
        "accepted_weight": 2,
        "accepted_signatures": [{"signer_id": "signer-0", "key_id": "key-0", "weight": 2}],
    }
    with pytest.raises(AssertionError, match="QUORUM FORGERY"):
        _assert_no_forgery(forged_under_threshold, threshold=5, active_ids=active_ids, weight_by_id=weight_by_id)

    forged_phantom = {
        "accepted_weight": 11,
        "accepted_signatures": [
            {"signer_id": "signer-0", "key_id": "key-0", "weight": 2},
            {"signer_id": "ghost", "key_id": "ghost-key", "weight": 9},
        ],
    }
    with pytest.raises(AssertionError, match="non-active/unregistered"):
        _assert_no_forgery(forged_phantom, threshold=5, active_ids=active_ids, weight_by_id=weight_by_id)


# (active?, weight). Weights are boundary-shaped: 1 and 2 (the smallest steps
# that can straddle a threshold) are over-sampled vs the uniform 1..5 fallback.
_weight_strategy = _boundary_int(1, 5, [1, 2, 5], repeat=3)
_quorum_signers = st.lists(
    st.tuples(st.booleans(), _weight_strategy), min_size=1, max_size=6
)


@settings(max_examples=3000, suppress_health_check=[HealthCheck.function_scoped_fixture])
@given(specs=_quorum_signers, env_pick=st.data())
def test_quorum_boundary_no_forgery_witness(specs, env_pick, _bls_oracle):
    n = len(specs)
    active_weight = sum(w for active, w in specs if active)
    if active_weight < 1:
        return  # no admissible registry (build rejects threshold > active_weight)

    # DISTRIBUTION SHAPING: drive the threshold to the knife-edge values around
    # the achievable-weight frontier so `accepted_weight == threshold` and
    # `accepted_weight == threshold - 1` become the COMMON case.
    threshold = env_pick.draw(
        _boundary_int(
            1,
            active_weight,
            [1, active_weight - 1, active_weight],
            repeat=5,
        )
    )

    signers = [
        {
            "signer_id": f"signer-{i}",
            "key_id": f"key-{i}",
            "public_key": PK(i + 1),
            "weight": w,
            "status": "active" if active else "revoked",
        }
        for i, (active, w) in enumerate(specs)
    ]
    registry = reg.build_signer_registry_v0(
        registry_id="rid-1", payload_kind=PAYLOAD_KIND, threshold=threshold, signers=signers
    )
    weight_by_id = {(f"signer-{i}", f"key-{i}"): w for i, (_a, w) in enumerate(specs)}
    active_ids = {(f"signer-{i}", f"key-{i}") for i, (a, _w) in enumerate(specs) if a}

    # Envelope pool: any registered index + an UNKNOWN signer; duplicates allowed.
    pool = list(range(n)) + [None]
    picks = env_pick.draw(st.lists(st.sampled_from(pool), min_size=1, max_size=n + 3))
    envelopes = []
    for k, idx in enumerate(picks):
        if idx is None:
            sid, kid = "ghost", f"ghost-key-{k}"
        else:
            sid, kid = f"signer-{idx}", f"key-{idx}"
        envelopes.append(
            {
                "signer_id": sid,
                "key_id": kid,
                "algorithm": BLS_ALG,
                "envelope_hash": "0x" + f"{k:064x}",
            }
        )

    # TARGET-GUIDED: the realised accepted weight of the *distinct active* picked
    # signers — steer the search so this sits as close to the threshold as
    # possible (the quorum knife-edge), where any off-by-one in `>=` lives.
    distinct_active = {
        idx for idx in picks if idx is not None and specs[idx][0]
    }
    realised_active_weight = sum(specs[idx][1] for idx in distinct_active)
    target(
        -abs(realised_active_weight - threshold),
        label="quorum: -|accepted_active_weight - threshold| (cluster at knife-edge)",
    )

    try:
        report = reg.verify_signature_quorum_v0(
            registry=registry,
            payload_kind=PAYLOAD_KIND,
            payload_hash=PAYLOAD_HASH,
            envelopes=envelopes,
        )
    except (ValueError, TypeError):
        return  # rejected — safe; no quorum certified

    _assert_no_forgery(report, threshold=threshold, active_ids=active_ids, weight_by_id=weight_by_id)

    report2 = reg.verify_signature_quorum_v0(
        registry=registry,
        payload_kind=PAYLOAD_KIND,
        payload_hash=PAYLOAD_HASH,
        envelopes=envelopes,
    )
    assert report2["quorum_report_hash"] == report["quorum_report_hash"]


# ===========================================================================
# B. BONDED SLASHING — knife-edges: slash == available, split residue maximal
# ===========================================================================
def _root(label: str) -> str:
    return hash_v0("boundary_slashing_mine_root", {"label": label})


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
    """Over/under/split-leak/phantom/collateral slash contract (identical to rung-1)."""
    before_entry = None
    for entry in registry_before["entries"]:
        if entry["subject_id"] == subject_id and entry["subject_kind"] == subject_kind:
            before_entry = entry
            break
    assert before_entry is not None, (
        f"PHANTOM SLASH: receipt slashed ({subject_id!r},{subject_kind!r}) with no matching bonded entry"
    )
    assert before_entry["status"] == "active", (
        f"PHANTOM SLASH: receipt slashed a non-active bond (status={before_entry['status']!r})"
    )
    assert evidence_height <= int(before_entry["slashable_until_height"]), (
        f"PHANTOM SLASH: evidence_height {evidence_height} outside slashability window "
        f"{before_entry['slashable_until_height']}"
    )

    bonded = int(before_entry["bonded_amount"])
    already = int(before_entry["slashed_amount"])
    available = bonded - already
    slash = int(receipt["slash_amount"])
    burn = int(receipt["burn_amount"])
    treasury = int(receipt["treasury_amount"])
    remaining = int(receipt["remaining_bond"])

    # INV-1: no over-slash
    assert slash > 0, f"zero/negative slash admitted: {slash}"
    assert slash <= available, (
        f"OVER-SLASH: slash {slash} > available bond {available} (bonded={bonded}, already_slashed={already})"
    )
    assert remaining == available - slash, f"remaining_bond {remaining} != available-slash {available - slash}"
    assert remaining >= 0, f"OVER-SLASH: negative remaining bond {remaining}"
    assert already + slash <= bonded, f"OVER-SLASH: cumulative slashed {already + slash} exceeds bond {bonded}"

    assert int(receipt["bonded_amount_before"]) == bonded
    assert int(receipt["already_slashed_before"]) == already

    # INV-2: split conservation (the residue knife-edge target stresses this floor)
    assert burn >= 0 and treasury >= 0, f"negative split (burn={burn},treasury={treasury})"
    assert burn + treasury == slash, f"SPLIT LEAK: burn {burn} + treasury {treasury} != slash {slash}"
    expected_burn = (slash * int(policy["burn_fraction_bps"])) // BPS
    assert burn == expected_burn, f"burn {burn} != floor(slash*burn_bps) {expected_burn}"

    # INV-3: policy bounds
    assert slash <= int(policy["max_slash_amount"]), (
        f"POLICY BREACH: slash {slash} > max_slash_amount {policy['max_slash_amount']}"
    )
    min_slash = int(policy["min_slash_amount"])
    if min_slash <= available:
        assert slash >= min_slash, (
            f"UNDER-SLASH: slash {slash} < policy min_slash_amount {min_slash} (available={available})"
        )

    # INV-4: only-subject mutation
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
            assert dict(after_e) == dict(before_e), (
                f"COLLATERAL SLASH: non-subject entry {sid!r} mutated: {dict(before_e)} -> {dict(after_e)}"
            )


def test_slash_teeth_catches_planted_violations():
    """Teeth / non-vacuity (same plants as rung-1): over-slash, split-leak,
    phantom, policy-breach, collateral, under-slash MUST each raise."""
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

    over = {"slash_amount": 5000, "burn_amount": 2500, "treasury_amount": 2500,
            "remaining_bond": 1000 - 5000, "bonded_amount_before": 1000,
            "already_slashed_before": 0, "evidence_hash": "0x" + "ab" * 32}
    with pytest.raises(AssertionError, match="OVER-SLASH"):
        _assert_no_overslash(receipt=over, updated_registry=good_after(5000),
                             registry_before=registry_before, policy=policy,
                             subject_id="s0", subject_kind="validator_set", evidence_height=7)

    leak = {"slash_amount": 100, "burn_amount": 50, "treasury_amount": 60,
            "remaining_bond": 900, "bonded_amount_before": 1000,
            "already_slashed_before": 0, "evidence_hash": "0x" + "ab" * 32}
    with pytest.raises(AssertionError, match="SPLIT LEAK"):
        _assert_no_overslash(receipt=leak, updated_registry=good_after(100),
                             registry_before=registry_before, policy=policy,
                             subject_id="s0", subject_kind="validator_set", evidence_height=7)

    phantom = {"slash_amount": 100, "burn_amount": 50, "treasury_amount": 50,
               "remaining_bond": 900, "bonded_amount_before": 1000,
               "already_slashed_before": 0, "evidence_hash": "0x" + "ab" * 32}
    with pytest.raises(AssertionError, match="PHANTOM SLASH"):
        _assert_no_overslash(receipt=phantom, updated_registry=good_after(100),
                             registry_before=registry_before, policy=policy,
                             subject_id="ghost", subject_kind="validator_set", evidence_height=7)

    breach = {"slash_amount": 300, "burn_amount": 150, "treasury_amount": 150,
              "remaining_bond": 700, "bonded_amount_before": 1000,
              "already_slashed_before": 0, "evidence_hash": "0x" + "ab" * 32}
    with pytest.raises(AssertionError, match="POLICY BREACH"):
        _assert_no_overslash(receipt=breach, updated_registry=good_after(300),
                             registry_before=registry_before, policy=policy,
                             subject_id="s0", subject_kind="validator_set", evidence_height=7)

    collateral_after = good_after(100)
    collateral_after["entries"][1]["slashed_amount"] = 99
    valid = {"slash_amount": 100, "burn_amount": 50, "treasury_amount": 50,
             "remaining_bond": 900, "bonded_amount_before": 1000,
             "already_slashed_before": 0, "evidence_hash": "0x" + "ab" * 32}
    with pytest.raises(AssertionError, match="COLLATERAL SLASH"):
        _assert_no_overslash(receipt=valid, updated_registry=collateral_after,
                             registry_before=registry_before, policy=policy,
                             subject_id="s0", subject_kind="validator_set", evidence_height=7)

    high_min_policy = {"max_slash_amount": 800, "min_slash_amount": 200, "burn_fraction_bps": 5000}
    under = {"slash_amount": 100, "burn_amount": 50, "treasury_amount": 50,
             "remaining_bond": 900, "bonded_amount_before": 1000,
             "already_slashed_before": 0, "evidence_hash": "0x" + "ab" * 32}
    with pytest.raises(AssertionError, match="UNDER-SLASH"):
        _assert_no_overslash(receipt=under, updated_registry=good_after(100),
                             registry_before=registry_before, policy=high_min_policy,
                             subject_id="s0", subject_kind="validator_set", evidence_height=7)


@settings(max_examples=2500, suppress_health_check=[HealthCheck.too_slow])
@given(
    # height/window pushed to the slashability-window knife-edge:
    #   admit iff height <= window. Anchors make window == height and
    #   window == height-1 (the off-by-one reject edge) the common case.
    height=_boundary_int(0, 30, [0, 1, 2], repeat=3),
    window_delta=_boundary_int(-2, 3, [-1, 0, 1], repeat=6),  # window = height + delta
    bonded=_boundary_int(1, 2000, [1, 2, 1999, 2000], repeat=3),
    # already-slashed shaped so available lands on small/boundary values
    available_target=_boundary_int(0, 2000, [0, 1, 2], repeat=4),
    slash_frac_bps=_boundary_int(0, BPS, [0, 1, 4999, 5000, 5001, BPS - 1, BPS], repeat=3),
    min_slash=_boundary_int(0, 3000, [0, 1, 2], repeat=3),
    max_slash=_boundary_int(1, 3000, [1, 2, 3000], repeat=3),
    # burn_bps shaped toward values that maximise the (slash*burn_bps) % BPS residue
    burn_bps=_boundary_int(0, BPS, [1, 3333, 6667, 9999, BPS - 1, BPS], repeat=3),
    status=st.sampled_from(["active", "slashed", "revoked"]),
    policy_status=st.sampled_from(["active", "revoked"]),
)
def test_slash_boundary_no_overslash_witness(
    height,
    window_delta,
    bonded,
    available_target,
    slash_frac_bps,
    min_slash,
    max_slash,
    burn_bps,
    status,
    policy_status,
):
    if min_slash > max_slash:  # build rejects min > max
        return
    window = height + window_delta
    if window < 0:
        return  # _require_nonnegative_int would reject; not a window-edge case
    # derive already-slashed so the *available* bond hits the boundary target,
    # clamped to a valid [0, bonded] range (build rejects already > bonded).
    already = bonded - min(available_target, bonded)
    if already < 0 or already > bonded:
        return

    evidence = _checkpoint_evidence(height=height, label_a="a", label_b="b")
    subject_id = str(evidence["subject_id"])
    decoy_id = _root("decoy-subject")

    registry = slash_mod.build_bond_registry_v0(
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
                "bonded_amount": 777,
                "slashed_amount": 0,
                "slashable_until_height": window,
                "status": "active",
                "processed_evidence_hashes": [],
            },
        ],
    )

    try:
        policy = slash_mod.build_slashing_policy_v0(
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
        return

    # TARGET-GUIDED #1: the slash the policy *would* compute (before the
    # available check) — steer so it equals the available bond exactly, the
    # over-slash knife-edge.
    available = bonded - already
    proportional = (bonded * slash_frac_bps) // BPS
    would_slash = min(max(proportional, min_slash), max_slash)
    target(
        -abs(would_slash - available),
        label="slash: -|computed_slash - available| (push slash to == available)",
    )
    # TARGET-GUIDED #2: maximise the burn-split rounding residue so the floor
    # split `burn + treasury == slash` is exercised at its worst rounding loss.
    target(
        float((would_slash * burn_bps) % BPS),
        label="slash: maximise (slash*burn_bps) % BPS (split-rounding residue)",
    )

    registry_snapshot = copy.deepcopy(registry)
    policy_snapshot = copy.deepcopy(policy)

    try:
        out = slash_mod.apply_bonded_slashing_v0(
            evidence=evidence, bond_registry=registry, policy=policy
        )
    except (ValueError, TypeError):
        assert registry == registry_snapshot, "reject mutated bond_registry input"
        assert policy == policy_snapshot, "reject mutated policy input"
        return

    receipt = out["receipt"]
    updated_registry = out["bond_registry"]

    _assert_no_overslash(
        receipt=receipt,
        updated_registry=updated_registry,
        registry_before=registry,
        policy=policy,
        subject_id=str(receipt["subject_id"]),
        subject_kind=str(receipt["subject_kind"]),
        evidence_height=int(receipt["evidence_height"]),
    )
    assert receipt["subject_id"] == subject_id, "receipt slashed the wrong subject"
    assert registry == registry_snapshot, "accept mutated caller's bond_registry input"
    assert policy == policy_snapshot, "accept mutated caller's policy input"

    out2 = slash_mod.apply_bonded_slashing_v0(
        evidence=copy.deepcopy(evidence),
        bond_registry=copy.deepcopy(registry_snapshot),
        policy=copy.deepcopy(policy_snapshot),
    )
    assert out2["receipt"]["receipt_hash"] == receipt["receipt_hash"], "non-deterministic receipt_hash"
    assert out2["receipt"]["bond_registry_hash_after"] == receipt["bond_registry_hash_after"], (
        "non-deterministic bond_registry_hash_after"
    )
    assert receipt["bond_registry_hash_after"] == updated_registry["bond_registry_hash"], (
        "receipt post-root does not bind the returned registry"
    )


def test_slash_boundary_admit_is_reachable():
    """Non-vacuity for the slash mine: a clean ADMIT at the slash==available
    boundary exists (slash 50 of a 100/50 bond -> remaining 0, status slashed)."""
    evidence = _checkpoint_evidence(height=5, label_a="a", label_b="b")
    registry = slash_mod.build_bond_registry_v0(
        chain_id=CHAIN_ID,
        asset_id="ZENO",
        entries=[
            {
                "subject_id": evidence["subject_id"],
                "subject_kind": "validator_set",
                "bonded_amount": 100,
                "slashed_amount": 50,
                "slashable_until_height": 100,
                "status": "active",
                "processed_evidence_hashes": [],
            }
        ],
    )
    policy = slash_mod.build_slashing_policy_v0(
        chain_id=CHAIN_ID,
        policy_id="p",
        evidence_kind=str(evidence["evidence_kind"]),
        slash_fraction_bps=5_000,  # 50% of bonded(100) == 50 == available
        min_slash_amount=1,
        max_slash_amount=3000,
        burn_fraction_bps=3_333,
    )
    out = slash_mod.apply_bonded_slashing_v0(evidence=evidence, bond_registry=registry, policy=policy)
    r = out["receipt"]
    assert r["slash_amount"] == 50 and r["remaining_bond"] == 0
    assert r["burn_amount"] + r["treasury_amount"] == r["slash_amount"]
    assert out["bond_registry"]["entries"][0]["status"] == "slashed"


# ===========================================================================
# C. VALIDATOR SCHEDULE — knife-edge: height at cycle wrap
#    offset % cycle_len == cycle_len - 1 (last slot) and == 0 (wrap to first)
# ===========================================================================
def test_schedule_teeth_catches_unfair_reference():
    """Teeth / non-vacuity: a BUGGY reference scheduler (clearly-marked) that uses
    `offset % n_validators` instead of `offset % active_slot_count` over-selects a
    high-power validator. The fairness invariant MUST reject it. This proves the
    fairness check has teeth and is not trivially satisfied."""
    # 2 validators, powers 1 and 3 -> cycle_len = 4, expected counts {v0:1, v1:3}.
    expected_power = {("val-0", "key-0"): 1, ("val-1", "key-1"): 3}
    cycle_len = 4

    def _buggy_proposer(offset: int):
        # BUGGY: index into the *validator list* (len 2) not the weighted slots.
        # This selects each validator equally (2 each over 4 heights), ignoring
        # voting power -> an unfair schedule.
        ordered = [("val-0", "key-0"), ("val-1", "key-1")]
        return ordered[offset % len(ordered)]

    counts: dict[tuple[str, str], int] = {}
    for offset in range(cycle_len):
        p = _buggy_proposer(offset)
        counts[p] = counts.get(p, 0) + 1
    # The buggy schedule gives {v0:2, v1:2}; the fairness invariant must reject it.
    with pytest.raises(AssertionError, match="unfair schedule"):
        assert counts == expected_power, (
            f"unfair schedule over cycle: got {counts} expected {expected_power}"
        )


# (active?, voting_power); powers shaped toward 1, 2, and the max 4 so the cycle
# length lands on small/boundary multiples and wrap edges are hit cheaply.
_power_strategy = _boundary_int(1, 4, [1, 2, 4], repeat=3)
_schedule_validators = st.lists(
    st.tuples(st.booleans(), _power_strategy), min_size=1, max_size=5
)


@settings(max_examples=2500)
@given(specs=_schedule_validators, start_height=_boundary_int(0, 5, [0, 1], repeat=3), env=st.data())
def test_schedule_boundary_no_selection_witness(specs, start_height, env):
    active = [(i, w) for i, (a, w) in enumerate(specs) if a]
    if not active:
        return  # build rejects a set with no active validator
    validators = [
        {
            "validator_id": f"val-{i}",
            "key_id": f"key-{i}",
            "public_key": PK(i + 1),
            "voting_power": w,
            "status": "active" if a else "revoked",
        }
        for i, (a, w) in enumerate(specs)
    ]
    vset = vs.build_validator_set_v0(
        chain_id="chain-1", epoch=0, start_height=start_height, validators=validators
    )
    active_ids = {(f"val-{i}", f"key-{i}") for i, _w in active}
    expected_power = {(f"val-{i}", f"key-{i}"): w for i, w in active}
    cycle_len = vset["active_slot_count"]  # sum of active voting power

    # DISTRIBUTION SHAPING + TARGET-GUIDED: probe a single boundary height whose
    # offset lands ON a wrap edge (last slot of a cycle, or first slot of the
    # next). Over-sample the wrap offsets and steer toward an exact wrap.
    wrap_anchors = [0, cycle_len - 1, cycle_len, 2 * cycle_len - 1, 2 * cycle_len]
    probe_offset = env.draw(_boundary_int(0, 3 * cycle_len + 1, wrap_anchors, repeat=5))
    probe_height = start_height + probe_offset
    pos_in_cycle = probe_offset % cycle_len
    # steer toward the last-slot wrap edge (cycle_len - 1): distance 0 there.
    target(
        -float(min(pos_in_cycle, cycle_len - 1 - pos_in_cycle)),
        label="schedule: push probe height onto a cycle-wrap slot",
    )

    # the boundary probe height: proposer must be active + deterministic.
    duty_probe = vs.build_proposer_duty_v0(validator_set=vset, height=probe_height)
    p_probe = (duty_probe["proposer"]["validator_id"], duty_probe["proposer"]["key_id"])
    assert p_probe in active_ids, f"out-of-set/revoked proposer {p_probe} at wrap height {probe_height}"
    duty_probe2 = vs.build_proposer_duty_v0(validator_set=vset, height=probe_height)
    assert duty_probe2["duty_hash"] == duty_probe["duty_hash"], "non-deterministic duty at wrap"
    # the slot index must itself be the modular position (binds the wrap math).
    assert int(duty_probe["slot_index"]) == pos_in_cycle, (
        f"slot_index {duty_probe['slot_index']} != offset%cycle_len {pos_in_cycle}"
    )
    assert int(duty_probe["cycle"]) == probe_offset // cycle_len, "cycle counter drift at wrap"

    # full-cycle fairness AROUND a wrap: walk exactly one cycle starting at the
    # probe's cycle start so the window straddles a wrap boundary.
    cycle_start = start_height + (probe_offset // cycle_len) * cycle_len
    counts: dict[tuple[str, str], int] = {}
    for h in range(cycle_start, cycle_start + cycle_len):
        duty = vs.build_proposer_duty_v0(validator_set=vset, height=h)
        p = (duty["proposer"]["validator_id"], duty["proposer"]["key_id"])
        assert p in active_ids, f"out-of-set/revoked proposer {p} at height {h}"
        counts[p] = counts.get(p, 0) + 1
    assert counts == expected_power, (
        f"unfair schedule over wrap-straddling cycle: got {counts} expected {expected_power}"
    )


def test_schedule_rejects_height_before_start():
    vset = vs.build_validator_set_v0(
        chain_id="c",
        epoch=0,
        start_height=10,
        validators=[{"validator_id": "v", "key_id": "k", "public_key": PK(1), "voting_power": 1}],
    )
    with pytest.raises(ValueError, match="precedes validator set start_height"):
        vs.build_proposer_duty_v0(validator_set=vset, height=9)
