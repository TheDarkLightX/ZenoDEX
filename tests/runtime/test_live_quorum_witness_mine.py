"""Symbolic disaster-witness mine for ZenoLedger LIVE-QUORUM ADMISSION FORGERY.

`build_live_checkpoint_quorum_admission_v0` (src/integration/zeno_ledger_live_quorum_v0.py)
is the live-finality admission gate. It COMPOSES three checks before emitting an
`ok=True, status="accepted"` admission:

  1. validate_checkpoint_header_binding_v0  — the checkpoint is exactly derived
     from the supplied header (no header/checkpoint substitution);
  2. canonical_header_hash_v0               — the payload the quorum signs is the
     admitted header's canonical hash (and the checkpoint's stored header_hash
     must equal it);
  3. verify_signature_quorum_v0             — the signer-quorum stake threshold is
     actually met over THAT header hash.

DISASTER CLASS — LIVE-QUORUM ADMISSION FORGERY:  a live checkpoint/header is
admitted (`ok=True`) WITHOUT the underlying signer-quorum threshold actually
being met over the admitted header's hash. Falsifiable safety invariants for any
accepted admission:

  INV-1  accepted_weight >= threshold                          (quorum cleared)
  INV-2  header_hash == checkpoint_header_hash                  (payload binding:
         == admission["checkpoint_header_hash"] == checkpoint["header_hash"]
         == canonical_header_hash_v0(header))   -> the signed payload IS the
         admitted header (no detached/substituted-payload admit)
  INV-3  the embedded quorum_report was verified over payload_hash == header_hash
         AND payload_kind == "checkpoint"        (no foreign-payload reuse)
  INV-4  accepted signatures are DISTINCT, ACTIVE, REGISTERED signers whose
         registry weights sum to accepted_weight (composition fabricates no weight)
  INV-5  admission["accepted_signature_count"] == len(accepted_signatures)
         and admission_hash recomputes deterministically (stable receipt)

And the negative/admission-implies-quorum direction:

  INV-6  if the underlying quorum verification would REJECT (missing /
         insufficient / duplicate / unregistered / under-threshold envelopes),
         admission MUST raise — it must NEVER return ok=True.

SCOPE / NON-CLAIMS:
  * The BLS per-envelope crypto check (validate_bls_signed_artifact_envelope_v0)
    is treated as a VALID-SIGNATURE ORACLE (stubbed to accept). Signature /
    aggregate forgery is OUT of scope and asserted nowhere here. We mine ONLY the
    composition / counting / threshold / payload-binding / determinism logic.
  * Single-admission only. Multi-checkpoint sequencing, replay across heights, and
    cross-module wiring (engine/state-root) are NOT covered.
  * A clean run over thousands of generated admissions is a bounded NEGATIVE
    receipt for this disaster class on the composition path.
"""

from __future__ import annotations

import pytest

hypothesis = pytest.importorskip("hypothesis")
from hypothesis import HealthCheck, given, settings  # noqa: E402
from hypothesis import strategies as st  # noqa: E402

from src.integration import zeno_ledger_live_quorum_v0 as m  # noqa: E402
from src.integration import zeno_ledger_signer_registry as reg  # noqa: E402
from src.integration import zeno_ledger_v0 as L  # noqa: E402


PK = lambda i: "0x" + f"{i:096x}"  # noqa: E731  canonical lowercase 48-byte hex
BLS_ALG = reg.SIGNED_ARTIFACT_ALGORITHM_BLS12_381_G2_BASIC_V0
PAYLOAD_KIND = "checkpoint"
ZERO_ROOT = "0x" + "00" * 32


@pytest.fixture(autouse=True)
def _bls_oracle(monkeypatch):
    """Stub the per-envelope BLS check to ACCEPT (valid-signature oracle).

    verify_signature_quorum_v0 calls the symbol bound in the signer-registry
    module namespace, so we patch it there. This isolates the search to the
    non-crypto composition / counting / threshold / payload-binding logic.
    """
    monkeypatch.setattr(
        reg, "validate_bls_signed_artifact_envelope_v0", lambda **_kw: None
    )


# ----------------------------------------------------------------------------- #
# VALID-input construction via the module's own build_* functions, then mutate. #
# ----------------------------------------------------------------------------- #
def _root(tag: str) -> str:
    # Distinct canonical 32-byte roots without touching BLS.
    return L.hash_v0("live_quorum_mine_root", {"tag": tag})


def _header(*, height: int = 6, label: str = "a") -> dict[str, object]:
    return L.build_header_v0(
        chain_id="zeno-ledger-live-quorum-mine-0",
        height=height,
        time_ms=1_778_730_000_000 + height,
        prev_header_hash=ZERO_ROOT,
        sequencer_set_hash=_root("validator-set"),
        ingress_root=_root(f"ingress-{label}"),
        tx_root=_root(f"tx-{label}"),
        pre_state_root=_root(f"pre-{label}"),
        post_state_root=_root(f"post-{label}"),
        app_hash=_root(f"app-{label}"),
        evidence_root=_root(f"evidence-{label}"),
        body_root=_root(f"body-{label}"),
        data_availability_root=_root(f"da-{label}"),
        proof_journal_hash=_root(f"proof-{label}"),
        config_digest=_root("config"),
        module_versions_digest=_root("modules"),
        signature_set_root=ZERO_ROOT,
    )


def _registry(specs):
    """Build a signer registry from (active?, weight) specs. Identity fixed by
    position. Returns (registry, active_ids, weight_by_id, active_weight)."""
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
    active_weight = sum(w for active, w in specs if active)
    return signers, active_weight


def _envelope(idx, k):
    """Hand-built envelope (no real BLS sign path). idx=None => unregistered."""
    if idx is None:
        sid, kid = "ghost", f"ghost-key-{k}"
    else:
        sid, kid = f"signer-{idx}", f"key-{idx}"
    return {
        "signer_id": sid,
        "key_id": kid,
        "algorithm": BLS_ALG,
        "envelope_hash": "0x" + f"{k:064x}",
    }


# ----------------------------------------------------------------------------- #
# The disaster-class invariant, factored out so the teeth test reuses it.        #
# ----------------------------------------------------------------------------- #
def _assert_no_admission_forgery(
    admission,
    *,
    header,
    checkpoint,
    threshold,
    active_ids,
    weight_by_id,
):
    """Raise AssertionError on any LIVE-QUORUM ADMISSION FORGERY.

    Encodes INV-1..INV-5 against an accepted admission. The teeth test plants a
    forged admission and asserts this trips.
    """
    assert admission.get("ok") is True
    assert admission.get("status") == "accepted"

    expected_hash = L.canonical_header_hash_v0(header)
    report = admission["quorum_report"]

    # INV-2: payload binding — every header-hash field agrees with the canonical
    # hash of the ADMITTED header and the checkpoint's stored header_hash.
    assert admission["header_hash"] == expected_hash, "admission header_hash drift"
    assert admission["checkpoint_header_hash"] == expected_hash, (
        "admission checkpoint_header_hash != canonical header hash"
    )
    assert checkpoint["header_hash"] == expected_hash, "checkpoint header_hash drift"

    # INV-3: the embedded quorum report was verified over THAT payload + kind.
    assert report["payload_hash"] == expected_hash, (
        f"ADMISSION FORGERY: quorum signed payload {report['payload_hash']} "
        f"!= admitted header hash {expected_hash}"
    )
    assert report["payload_kind"] == PAYLOAD_KIND, "quorum payload_kind drift"

    # INV-4: accepted set is distinct, active, registered; weights sum exactly.
    accepted = report["accepted_signatures"]
    ids = [(s["signer_id"], s["key_id"]) for s in accepted]
    assert len(ids) == len(set(ids)), f"double-counted signer in admit: {ids}"
    for ident in ids:
        assert ident in active_ids, f"admit counted non-active/unregistered {ident}"
    expect_w = sum(weight_by_id[i] for i in ids)
    assert report["accepted_weight"] == expect_w, (
        f"weight fabrication: report={report['accepted_weight']} recomputed={expect_w}"
    )
    assert admission["accepted_weight"] == report["accepted_weight"], "weight copy drift"

    # INV-5: count field matches; INV-1: quorum actually cleared.
    assert admission["accepted_signature_count"] == len(accepted), "count drift"
    assert admission["threshold"] == threshold, "threshold copy drift"
    assert admission["accepted_weight"] >= threshold, (
        f"ADMISSION FORGERY: accepted at weight {admission['accepted_weight']} "
        f"< threshold {threshold}"
    )


# ============================== TEETH / NON-VACUITY ============================ #
def test_invariant_catches_forged_admission():
    """Deterministic teeth: a forged admission whose quorum did NOT clear the
    threshold (and whose payload is detached from the admitted header) MUST trip
    `_assert_no_admission_forgery`. If this passes silently, the negative receipt
    below is a false receipt.
    """
    header = _header()
    checkpoint = L.build_checkpoint_v0(header)
    header_hash = checkpoint["header_hash"]
    active_ids = {("signer-0", "key-0")}
    weight_by_id = {("signer-0", "key-0"): 1}

    # Forgery A: under-threshold admit (weight 1, threshold 5) — the core
    # finality forgery: a checkpoint admitted without quorum stake.
    forged_under_threshold = {
        "ok": True,
        "status": "accepted",
        "header_hash": header_hash,
        "checkpoint_header_hash": header_hash,
        "threshold": 5,
        "accepted_weight": 1,
        "accepted_signature_count": 1,
        "quorum_report": {
            "payload_hash": header_hash,
            "payload_kind": PAYLOAD_KIND,
            "accepted_weight": 1,
            "accepted_signatures": [
                {"signer_id": "signer-0", "key_id": "key-0", "weight": 1}
            ],
        },
    }
    with pytest.raises(AssertionError, match="ADMISSION FORGERY"):
        _assert_no_admission_forgery(
            forged_under_threshold,
            header=header,
            checkpoint=checkpoint,
            threshold=5,
            active_ids=active_ids,
            weight_by_id=weight_by_id,
        )

    # Forgery B: detached payload — quorum cleared the threshold but over a
    # DIFFERENT (foreign) payload than the admitted header. A naive composition
    # that forgot to bind payload_hash := header_hash would emit this.
    other_hash = "0x" + "ee" * 32
    forged_detached = {
        "ok": True,
        "status": "accepted",
        "header_hash": header_hash,
        "checkpoint_header_hash": header_hash,
        "threshold": 1,
        "accepted_weight": 9,
        "accepted_signature_count": 1,
        "quorum_report": {
            "payload_hash": other_hash,  # signed a foreign payload!
            "payload_kind": PAYLOAD_KIND,
            "accepted_weight": 9,
            "accepted_signatures": [
                {"signer_id": "signer-0", "key_id": "key-0", "weight": 9}
            ],
        },
    }
    with pytest.raises(AssertionError, match="ADMISSION FORGERY"):
        _assert_no_admission_forgery(
            forged_detached,
            header=header,
            checkpoint=checkpoint,
            threshold=1,
            active_ids=active_ids,
            weight_by_id={("signer-0", "key-0"): 9},
        )

    # Forgery C: phantom (unregistered) signer fabricated into the accepted set.
    forged_phantom = {
        "ok": True,
        "status": "accepted",
        "header_hash": header_hash,
        "checkpoint_header_hash": header_hash,
        "threshold": 1,
        "accepted_weight": 1,
        "accepted_signature_count": 1,
        "quorum_report": {
            "payload_hash": header_hash,
            "payload_kind": PAYLOAD_KIND,
            "accepted_weight": 1,
            "accepted_signatures": [
                {"signer_id": "ghost", "key_id": "ghost-key", "weight": 1}
            ],
        },
    }
    with pytest.raises(AssertionError, match="non-active/unregistered"):
        _assert_no_admission_forgery(
            forged_phantom,
            header=header,
            checkpoint=checkpoint,
            threshold=1,
            active_ids=active_ids,
            weight_by_id={("signer-0", "key-0"): 1, ("ghost", "ghost-key"): 1},
        )


# =============================== THE MINE ===================================== #
@settings(
    max_examples=900,
    suppress_health_check=[HealthCheck.function_scoped_fixture, HealthCheck.too_slow],
)
@given(
    specs=st.lists(
        st.tuples(st.booleans(), st.integers(min_value=1, max_value=5)),
        min_size=1,
        max_size=6,
    ),
    pick=st.data(),
)
def test_live_quorum_admission_has_no_forgery_witness(specs, pick):
    """Build a VALID registry + header + checkpoint, then feed an adversarial
    envelope set (subset / duplicates / unregistered / over-full) into the
    admission composer. Any ok=True admit must satisfy INV-1..INV-5; any input
    the quorum would reject must raise (INV-6). No witness => bounded negative
    receipt for the admission-forgery disaster class on the composition path.
    """
    signers, active_weight = _registry(specs)
    if active_weight < 1:
        return  # build rejects threshold > active_weight; no admissible registry

    threshold = pick.draw(st.integers(min_value=1, max_value=active_weight))
    registry = reg.build_signer_registry_v0(
        registry_id="rid-live-1",
        payload_kind=PAYLOAD_KIND,
        threshold=threshold,
        signers=signers,
    )
    n = len(specs)
    weight_by_id = {(f"signer-{i}", f"key-{i}"): w for i, (_a, w) in enumerate(specs)}
    active_ids = {(f"signer-{i}", f"key-{i}") for i, (a, _w) in enumerate(specs) if a}

    header = _header()
    checkpoint = L.build_checkpoint_v0(header)

    # Adversarial envelope pool: any registered index, an UNREGISTERED identity,
    # and duplicates are allowed. The signed payload is the REAL header hash, but
    # the membership/weight/dedup logic is what we attack.
    pool = list(range(n)) + [None]
    picks = pick.draw(st.lists(st.sampled_from(pool), min_size=1, max_size=n + 3))
    envelopes = [_envelope(idx, k) for k, idx in enumerate(picks)]

    try:
        admission = m.build_live_checkpoint_quorum_admission_v0(
            header=header,
            checkpoint=checkpoint,
            registry=registry,
            envelopes=envelopes,
        )
    except (ValueError, TypeError):
        return  # INV-6: rejected — safe, no checkpoint admitted

    # ---- ADMIT: the no-forgery invariant must hold ----
    _assert_no_admission_forgery(
        admission,
        header=header,
        checkpoint=checkpoint,
        threshold=threshold,
        active_ids=active_ids,
        weight_by_id=weight_by_id,
    )

    # Round-trip validator must accept its own admission (binding consistency).
    m.validate_live_checkpoint_quorum_admission_v0(
        admission=admission,
        header=header,
        checkpoint=checkpoint,
        registry=registry,
        envelopes=envelopes,
    )

    # Determinism: identical inputs -> identical admission receipt.
    admission2 = m.build_live_checkpoint_quorum_admission_v0(
        header=header,
        checkpoint=checkpoint,
        registry=registry,
        envelopes=envelopes,
    )
    assert admission2["admission_hash"] == admission["admission_hash"], "nondeterministic admit"
    assert admission2["quorum_report_hash"] == admission["quorum_report_hash"]


# ===================== BOUNDARY / REJECT (admission-implies-quorum) ============ #
def test_admission_rejects_below_threshold_envelope_set():
    """INV-1/INV-6 boundary: a single-signer envelope set against a threshold-2
    registry MUST raise 'threshold not met' — never an ok=True admit."""
    signers, active_weight = _registry([(True, 1), (True, 1)])
    assert active_weight == 2
    registry = reg.build_signer_registry_v0(
        registry_id="rid-boundary",
        payload_kind=PAYLOAD_KIND,
        threshold=2,
        signers=signers,
    )
    header = _header()
    checkpoint = L.build_checkpoint_v0(header)
    with pytest.raises(ValueError, match="threshold not met"):
        m.build_live_checkpoint_quorum_admission_v0(
            header=header,
            checkpoint=checkpoint,
            registry=registry,
            envelopes=[_envelope(0, 0)],  # only weight 1 < threshold 2
        )


def test_admission_rejects_header_checkpoint_substitution():
    """INV-2/INV-6: a checkpoint derived from a DIFFERENT header MUST be rejected
    (binding mismatch) — no payload-substitution admit."""
    header = _header(label="a")
    checkpoint = L.build_checkpoint_v0(_header(label="b"))
    signers, _ = _registry([(True, 1), (True, 1)])
    registry = reg.build_signer_registry_v0(
        registry_id="rid-sub",
        payload_kind=PAYLOAD_KIND,
        threshold=1,
        signers=signers,
    )
    with pytest.raises(ValueError, match="checkpoint/header binding mismatch"):
        m.build_live_checkpoint_quorum_admission_v0(
            header=header,
            checkpoint=checkpoint,
            registry=registry,
            envelopes=[_envelope(0, 0)],
        )
