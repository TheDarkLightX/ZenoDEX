"""Symbolic disaster-witness mine for ZenoLedger signature-quorum *counting*.

`verify_signature_quorum_v0` is the consensus-finality gate: a checkpoint / live
header is admitted only if a set of signature envelopes clears the registry's
stake threshold. The per-envelope BLS check lives in
`validate_bls_signed_artifact_envelope_v0` (the crypto layer, owned elsewhere); the
*counting* logic — active-signer filtering, identity and public-key dedup, weight
summation, and the `weight >= threshold` gate — is the consensus-critical part and
had only example-based tests.

This treats the BLS check as a "valid signature" ORACLE (stubbed to accept) and
uses `hypothesis` to search for a counting witness for the disaster class:

    QUORUM FORGERY:  admit  ⟹  the accepted set is DISTINCT by identity and
    public key, contains only ACTIVE registry signers whose registry weights
    sum to accepted_weight, and
    accepted_weight >= threshold.

Any admit that violates this is a finality forgery (a quorum certified with less
than the required honest stake, a revoked/unregistered signer counted, or a
double-counted signer). A clean run over thousands of generated registries is a
bounded NEGATIVE receipt for that disaster class on the counting path.

The crypto path (signature/aggregate forgery) is explicitly OUT of scope here and
is asserted nowhere in this test.
"""

from __future__ import annotations

import pytest

hypothesis = pytest.importorskip("hypothesis")
from hypothesis import HealthCheck, given, settings  # noqa: E402
from hypothesis import strategies as st  # noqa: E402

from src.integration import zeno_ledger_signer_registry as reg  # noqa: E402

PK = lambda i: "0x" + f"{i:096x}"  # noqa: E731  canonical lowercase 48-byte hex
BLS_ALG = reg.SIGNED_ARTIFACT_ALGORITHM_BLS12_381_G2_BASIC_V0
PAYLOAD_KIND = "checkpoint"
PAYLOAD_HASH = "0x" + "ab" * 32


@pytest.fixture(autouse=True)
def _bls_oracle(monkeypatch):
    """Stub the BLS check to ACCEPT (valid-signature oracle), so the property
    search exercises only the counting/dedup/threshold/active-filter logic."""
    monkeypatch.setattr(
        reg, "validate_bls_signed_artifact_envelope_v0", lambda **_kw: None
    )


# A signer slice: (active?, weight in 1..5, aliased key slot). Identity i is
# fixed by position while key slots deliberately collide across identities.
_signers = st.lists(
    st.tuples(
        st.booleans(),
        st.integers(min_value=1, max_value=5),
        st.integers(min_value=0, max_value=2),
    ),
    min_size=1,
    max_size=6,
)


def _assert_no_forgery(report, *, threshold, active_ids, weight_by_id, public_key_by_id):
    """The quorum-forgery invariant, factored out so the teeth test can reuse it.

    Raises AssertionError on any forgery: double-count, non-active/unregistered
    signer counted, phantom weight, or certified weight below threshold."""
    accepted = report["accepted_signatures"]
    ids = [(s["signer_id"], s["key_id"]) for s in accepted]
    assert len(ids) == len(set(ids)), f"double-counted signer in admit: {ids}"
    public_keys = [public_key_by_id[identity] for identity in ids]
    assert len(public_keys) == len(set(public_keys)), (
        f"double-counted BLS public key in admit: {public_keys}"
    )
    for ident in ids:
        assert ident in active_ids, f"admit counted non-active/unregistered {ident}"
    expect_w = sum(weight_by_id[i] for i in ids)
    assert report["accepted_weight"] == expect_w, (
        f"weight mismatch: report={report['accepted_weight']} recomputed={expect_w}"
    )
    assert report["accepted_weight"] >= threshold, (
        f"QUORUM FORGERY: admit at weight {report['accepted_weight']} < threshold {threshold}"
    )


def test_invariant_catches_forged_certificate():
    """Teeth / non-vacuity: a forged report (weight below threshold, and a phantom
    revoked signer) MUST trip the checker. If this passes silently, the negative
    receipt below would be meaningless."""
    active_ids = {("signer-0", "key-0")}
    weight_by_id = {("signer-0", "key-0"): 2, ("ghost", "ghost-key"): 9}
    public_key_by_id = {("signer-0", "key-0"): PK(1), ("ghost", "ghost-key"): PK(2)}
    forged_under_threshold = {
        "accepted_weight": 2,
        "accepted_signatures": [{"signer_id": "signer-0", "key_id": "key-0", "weight": 2}],
    }
    with pytest.raises(AssertionError, match="QUORUM FORGERY"):
        _assert_no_forgery(
            forged_under_threshold,
            threshold=5,
            active_ids=active_ids,
            weight_by_id=weight_by_id,
            public_key_by_id=public_key_by_id,
        )

    forged_phantom_signer = {
        "accepted_weight": 11,
        "accepted_signatures": [
            {"signer_id": "signer-0", "key_id": "key-0", "weight": 2},
            {"signer_id": "ghost", "key_id": "ghost-key", "weight": 9},
        ],
    }
    with pytest.raises(AssertionError, match="non-active/unregistered"):
        _assert_no_forgery(
            forged_phantom_signer,
            threshold=5,
            active_ids=active_ids,
            weight_by_id=weight_by_id,
            public_key_by_id=public_key_by_id,
        )

    duplicate_key_report = {
        "accepted_weight": 4,
        "accepted_signatures": [
            {"signer_id": "signer-0", "key_id": "key-0", "weight": 2},
            {"signer_id": "signer-1", "key_id": "key-1", "weight": 2},
        ],
    }
    duplicate_key_ids = {("signer-0", "key-0"), ("signer-1", "key-1")}
    duplicate_key_weights = {identity: 2 for identity in duplicate_key_ids}
    duplicate_public_keys = {identity: PK(1) for identity in duplicate_key_ids}
    with pytest.raises(AssertionError, match="double-counted BLS public key"):
        _assert_no_forgery(
            duplicate_key_report,
            threshold=4,
            active_ids=duplicate_key_ids,
            weight_by_id=duplicate_key_weights,
            public_key_by_id=duplicate_public_keys,
        )


@settings(
    max_examples=2000,
    suppress_health_check=[HealthCheck.function_scoped_fixture, HealthCheck.too_slow],
)
@given(specs=_signers, env_pick=st.data())
def test_quorum_counting_has_no_forgery_witness(specs, env_pick):
    n = len(specs)
    active_weight = sum(w for active, w, _key_slot in specs if active)
    if active_weight < 1:
        return  # no admissible registry exists (build rejects threshold>active_weight)

    threshold = env_pick.draw(st.integers(min_value=1, max_value=active_weight))
    signers = [
        {
            "signer_id": f"signer-{i}",
            "key_id": f"key-{i}",
            "public_key": PK(key_slot + 1),
            "weight": w,
            "status": "active" if active else "revoked",
        }
        for i, (active, w, key_slot) in enumerate(specs)
    ]
    try:
        registry = reg.build_signer_registry_v0(
            registry_id="rid-1", payload_kind=PAYLOAD_KIND, threshold=threshold, signers=signers
        )
    except ValueError as exc:
        if len({key_slot for _active, _weight, key_slot in specs}) < n:
            assert str(exc) == "duplicate signer public_key"
            return
        raise
    weight_by_id = {
        (f"signer-{i}", f"key-{i}"): w for i, (_a, w, _key_slot) in enumerate(specs)
    }
    public_key_by_id = {
        (f"signer-{i}", f"key-{i}"): PK(key_slot + 1)
        for i, (_a, _w, key_slot) in enumerate(specs)
    }
    active_ids = {
        (f"signer-{i}", f"key-{i}")
        for i, (active, _weight, _key_slot) in enumerate(specs)
        if active
    }

    # Envelope pool: any registered index, an UNKNOWN signer, and allow duplicates.
    pool = list(range(n)) + [None]  # None => unregistered identity
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

    try:
        report = reg.verify_signature_quorum_v0(
            registry=registry,
            payload_kind=PAYLOAD_KIND,
            payload_hash=PAYLOAD_HASH,
            envelopes=envelopes,
        )
    except (ValueError, TypeError):
        return  # rejected — safe; no quorum certified

    # ---- ADMIT: the no-forgery invariant must hold (distinct + active +
    # exact weight + clears threshold) ----
    _assert_no_forgery(
        report,
        threshold=threshold,
        active_ids=active_ids,
        weight_by_id=weight_by_id,
        public_key_by_id=public_key_by_id,
    )

    # determinism: identical inputs -> identical certificate
    report2 = reg.verify_signature_quorum_v0(
        registry=registry,
        payload_kind=PAYLOAD_KIND,
        payload_hash=PAYLOAD_HASH,
        envelopes=envelopes,
    )
    assert report2["quorum_report_hash"] == report["quorum_report_hash"]
