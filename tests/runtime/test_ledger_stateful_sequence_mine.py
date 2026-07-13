"""STATEFUL multi-transition disaster mine for two ZenoLedger consensus surfaces.

Rung 2 of the input-generation ladder. The prior rung-1 mines
(`test_ledger_schedule_conflict_witness_mine.py`,
`test_signer_quorum_counting_witness_mine.py`,
`test_dynamic_peers_witness_mine.py`) drew UNIFORM-RANDOM SINGLE-SHOT inputs:
one registry, one envelope set, one admission. They cannot reach disasters that
only emerge from a SEQUENCE of transitions threaded through evolving state.

This file uses `hypothesis.stateful.RuleBasedStateMachine` to drive MULTIPLE
transitions against state carried forward between steps, targeting the
MULTI-TRANSITION disaster classes that single-shot mining structurally misses:

  A. BondedSlashingMachine  (apply_bonded_slashing_v0)
     - DOUBLE-SLASH VIA EVIDENCE REPLAY: applying the SAME evidence hash twice,
       or many DISTINCT-but-overlapping evidence packets naming the SAME subject,
       across a sequence drives cumulative slashed past the bond.
     - REGISTRY NON-MONOTONICITY / RESURRECTION: a subject's slashed_amount must
       never decrease and a slashed/depleted entry must never come back to life
       across the whole run.
     Cross-run @invariant: for every subject, cumulative slashed <= original bond;
     per-subject slashed is monotonic non-decreasing; a replayed (already-processed)
     evidence hash is a STRICT no-op (rejected, no slashed increase); the threaded
     registry always re-validates and its hash binds.

  B. DynamicPeerMachine  (build_dynamic_peer_admission_v0)
     - PEER-SET UNBOUNDED ACCUMULATION across REPEATED admission rounds: the prior
       round's final set becomes the next round's current set, with a fresh
       candidate each round. Single-shot mining only ever does one fold (and one
       idempotent re-fold). Here we fold dozens of times.
     Cross-run @invariant: the final set stays bounded (<= cap), strictly
     deduplicated, and monotonic across rounds (no silent drop, no unbounded
     growth, never exceeds the operator cap on any reachable round).

A clean run is a bounded NEGATIVE receipt for these multi-transition disaster
classes. A real witness (cumulative slash > bond, resurrection, unbounded set,
silent drop) is a CRITICAL finding to REPORT, not patch.

The teeth tests plant forged sequence outcomes and assert the cross-run
invariant checkers RAISE — proving the mine is non-vacuous.
"""

from __future__ import annotations

import copy

import pytest

hypothesis = pytest.importorskip("hypothesis")
from hypothesis import HealthCheck, settings  # noqa: E402
from hypothesis import strategies as st  # noqa: E402
from hypothesis.stateful import (  # noqa: E402
    RuleBasedStateMachine,
    invariant,
    precondition,
    rule,
    run_state_machine_as_test,
)

from src.integration import zeno_ledger_dynamic_peers_v0 as peers  # noqa: E402
from src.integration.zeno_ledger_anti_equivocation_v0 import (  # noqa: E402
    build_checkpoint_equivocation_slashing_evidence_v0,
    build_watcher_attestation_equivocation_slashing_evidence_v0,
)
from src.integration.zeno_ledger_bonded_slashing_v0 import (  # noqa: E402
    apply_bonded_slashing_v0,
    build_bond_registry_v0,
    build_slashing_policy_v0,
    validate_bond_registry_v0,
)
from src.integration.zeno_ledger_v0 import (  # noqa: E402
    build_checkpoint_v0,
    build_header_v0,
    hash_v0,
)
from src.integration.zeno_ledger_watcher import build_watcher_attestation_v0  # noqa: E402

CHAIN_ID = "zeno-ledger-stateful-testnet-0"
ASSET_ID = "ZENO"
ZERO_ROOT = "0x" + "00" * 32

# Bond / policy parameters used by the slashing machine. slash_fraction_bps=1000
# (10%) of a 1000-unit bond => 100 per slash; min/max keep every slash at 100.
# So an HONEST ledger admits AT MOST 10 slashes per subject before the bond is
# depleted and the entry flips to "slashed" (further slashes must reject). The
# stateful machine fires far more than 10 fresh-evidence rules per subject,
# guaranteeing it drives the registry into the depletion / replay-reject regime
# many times over — the exact multi-transition region rung-1 cannot reach.
BONDED_AMOUNT = 1_000
SLASH_FRACTION_BPS = 1_000
SLASH_PER_HIT = (BONDED_AMOUNT * SLASH_FRACTION_BPS) // 10_000  # == 100
MAX_HITS_BEFORE_DEPLETION = BONDED_AMOUNT // SLASH_PER_HIT  # == 10


def _root(label: str) -> str:
    return hash_v0("test_root", {"label": label})


def _header(*, vset_label: str, height: int, body_label: str) -> dict[str, object]:
    """A canonical header. `vset_label` fixes the sequencer_set_hash (==subject_id
    for checkpoint evidence); `body_label` varies the rest so two headers at the
    same (vset, height) genuinely conflict and produce a fresh evidence_hash."""
    return build_header_v0(
        chain_id=CHAIN_ID,
        height=height,
        time_ms=1_778_730_000_000 + height,
        prev_header_hash=ZERO_ROOT,
        sequencer_set_hash=_root(f"validator-set-{vset_label}"),
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


def _checkpoint_evidence(*, vset_label: str, height: int, variant: int) -> dict[str, object]:
    """A fresh, valid checkpoint-equivocation evidence packet for the SAME subject
    (fixed by vset_label) at a fixed height. Different `variant` -> a conflicting
    second header -> a DISTINCT evidence_hash naming the same subject_id."""
    checkpoint_a = build_checkpoint_v0(_header(vset_label=vset_label, height=height, body_label="a"))
    checkpoint_b = build_checkpoint_v0(
        _header(vset_label=vset_label, height=height, body_label=f"b{variant}")
    )
    return build_checkpoint_equivocation_slashing_evidence_v0(checkpoint_a, checkpoint_b)


def _verify_report(*, from_height: int, to_height: int, tip: str) -> dict[str, object]:
    return {
        "schema": "zenodex.zeno_ledger.verify_report.v0",
        "ok": True,
        "status": "range_verified",
        "mode": "replay_bound",
        "authority_scope": "replay_bound_range_v0",
        "range_verified": True,
        "header_linkage_checked": True,
        "state_continuity_checked": True,
        "state_replay_checked": True,
        "receipt_replay_checked": True,
        "config_binding_checked": True,
        "replay_config_digest": _root("replay-config"),
        "checked_heights": list(range(from_height, to_height + 1)),
        "proof_metadata_checked_heights": [],
        "proof_verification_checked_heights": [],
        "last_header_hash": _root(tip),
        "last_post_state_root": _root(f"post-{tip}"),
        "last_app_hash": _root(f"app-{tip}"),
        "errors": [],
    }


def _watcher_evidence(*, profile_label: str, variant: int) -> dict[str, object]:
    """A fresh, valid watcher-equivocation evidence packet for the SAME subject
    (the watcher profile_id, fixed by watcher_id 'wa') at a fixed tip height.
    Different `variant` varies the conflicting tip hash -> a DISTINCT evidence_hash
    naming the same subject_id."""
    attestation_a = build_watcher_attestation_v0(
        verify_report=_verify_report(from_height=3, to_height=8, tip=f"tip-a-{profile_label}"),
        watcher_id="wa",
        observed_time_ms=1,
        verifier_ref="python:zeno_ledger_verify:v0",
    )
    attestation_b = build_watcher_attestation_v0(
        verify_report=_verify_report(from_height=5, to_height=8, tip=f"tip-b-{profile_label}-{variant}"),
        watcher_id="wb",
        observed_time_ms=2,
        verifier_ref="python:zeno_ledger_verify:v0",
    )
    return build_watcher_attestation_equivocation_slashing_evidence_v0(attestation_a, attestation_b)


def _policy_for(evidence_kind: str) -> dict[str, object]:
    return build_slashing_policy_v0(
        chain_id=CHAIN_ID,
        policy_id=f"slashing-policy-{evidence_kind}",
        evidence_kind=evidence_kind,
        slash_fraction_bps=SLASH_FRACTION_BPS,
        min_slash_amount=1,
        max_slash_amount=200,
        burn_fraction_bps=5_000,
    )


# Pre-build a deterministic pool of distinct evidence packets per subject so the
# rules can pick fresh OR replayed evidence cheaply (building checkpoints inside
# every step would be slow). Each pool entry is a valid, distinct-hash packet for
# the SAME subject. _POOL_SIZE > MAX_HITS_BEFORE_DEPLETION so the machine can keep
# feeding fresh evidence well past bond depletion.
_POOL_SIZE = 16

# subject_key -> (evidence_kind, subject_kind, [evidence packets...])
_CHECKPOINT_SUBJECT = "checkpoint"
_WATCHER_SUBJECT = "watcher"

_EVIDENCE_POOLS: dict[str, dict[str, object]] = {
    _CHECKPOINT_SUBJECT: {
        "evidence_kind": "checkpoint_equivocation",
        "subject_kind": "validator_set",
        "packets": [
            _checkpoint_evidence(vset_label="cp", height=7, variant=v) for v in range(_POOL_SIZE)
        ],
    },
    _WATCHER_SUBJECT: {
        "evidence_kind": "watcher_attestation_equivocation",
        "subject_kind": "watcher_profile",
        "packets": [_watcher_evidence(profile_label="wp", variant=v) for v in range(_POOL_SIZE)],
    },
}

_POLICIES = {
    _CHECKPOINT_SUBJECT: _policy_for("checkpoint_equivocation"),
    _WATCHER_SUBJECT: _policy_for("watcher_attestation_equivocation"),
}


# --------------------------------------------------------------------------- #
# Cross-run invariant checkers (factored out so the teeth tests can reuse them).
# These RAISE AssertionError on any multi-transition disaster.
# --------------------------------------------------------------------------- #
def assert_cumulative_slash_safe(
    *,
    subject_key: str,
    bonded: int,
    cumulative_slashed: int,
    entry_slashed: int,
    prev_entry_slashed: int,
    entry_status: str,
) -> None:
    """The double-slash / non-monotonicity / resurrection invariant.

    Raises AssertionError on:
      - cumulative slashed across the whole run exceeding the original bond
        (DOUBLE-SLASH VIA REPLAY),
      - the registry entry's slashed_amount disagreeing with the externally
        tracked cumulative (ledger drift),
      - a non-monotonic slashed_amount (RESURRECTION to a lower value),
      - a depleted entry (slashed == bonded) not reporting "slashed" status, or a
        non-depleted entry being marked "slashed" (status drift).
    """
    assert cumulative_slashed <= bonded, (
        f"DOUBLE-SLASH: subject {subject_key} cumulative slashed {cumulative_slashed} "
        f"exceeds original bond {bonded}"
    )
    assert entry_slashed == cumulative_slashed, (
        f"LEDGER DRIFT: subject {subject_key} registry slashed {entry_slashed} != "
        f"externally tracked cumulative {cumulative_slashed}"
    )
    assert entry_slashed >= prev_entry_slashed, (
        f"NON-MONOTONIC / RESURRECTION: subject {subject_key} slashed dropped from "
        f"{prev_entry_slashed} to {entry_slashed}"
    )
    assert entry_slashed <= bonded, (
        f"OVER-SLASH: subject {subject_key} registry slashed {entry_slashed} > bond {bonded}"
    )
    if entry_slashed == bonded:
        assert entry_status == "slashed", (
            f"DEPLETED-BUT-ACTIVE: subject {subject_key} fully slashed but status {entry_status!r}"
        )
    else:
        assert entry_status == "active", (
            f"STATUS DRIFT: subject {subject_key} not depleted but status {entry_status!r}"
        )


def assert_peer_round_safe(
    *,
    prev_final: list[str],
    new_final: list[str],
    cap: int,
    round_index: int,
) -> None:
    """The peer-set-accumulation invariant across admission rounds.

    Raises AssertionError on:
      - the final set exceeding the operator cap (UNBOUNDED ACCUMULATION),
      - a duplicate in the final set (dedup failed across rounds),
      - any peer present in the prior round's final set missing from the new final
        set (SILENT DROP / non-monotonic peer registry),
      - the final set shrinking in length (monotone-growth violation).
    """
    assert len(new_final) <= cap, (
        f"UNBOUNDED PEER SET: round {round_index} final_peer_count {len(new_final)} "
        f"> max_peer_count {cap}"
    )
    assert len(new_final) == len(set(new_final)), (
        f"DUPLICATE peer in round {round_index} final set: {new_final}"
    )
    for url in prev_final:
        assert url in new_final, (
            f"SILENT DROP: peer {url} present in round {round_index - 1} final set "
            f"missing from round {round_index} final set {new_final}"
        )
    assert len(new_final) >= len(prev_final), (
        f"PEER SET SHRANK: round {round_index} len {len(new_final)} < "
        f"round {round_index - 1} len {len(prev_final)}"
    )


def assert_peer_admission_delta_safe(
    *,
    prev_final: list[str],
    candidate_urls: list[str],
    admitted: list[str],
    new_final: list[str],
    round_index: int,
) -> None:
    """The per-round provenance invariant.

    Raises AssertionError on:
      - a phantom admitted peer not present in the canonical candidate list,
      - re-counting an already-current peer as newly admitted,
      - a final set that is anything other than prior peers followed by the
        canonical new candidate delta.
    """
    prev_set = set(prev_final)
    expected_admitted = [url for url in candidate_urls if url not in prev_set]
    assert admitted == expected_admitted, (
        f"ADMISSION DELTA DRIFT: round {round_index} admitted {admitted} "
        f"!= expected new candidate delta {expected_admitted}"
    )
    expected_final = peers.canonical_peer_urls_v0([*prev_final, *expected_admitted], name="expected_final")
    assert new_final == expected_final, (
        f"FINAL PEER PROVENANCE DRIFT: round {round_index} final {new_final} "
        f"!= prior peers plus admitted delta {expected_final}"
    )


# =========================================================================== #
# A. Bonded-slashing stateful machine.
# =========================================================================== #
class BondedSlashingMachine(RuleBasedStateMachine):
    """Drives a SEQUENCE of apply_bonded_slashing_v0 transitions against an
    evolving bond_registry shared by two subjects (a validator_set and a
    watcher_profile). The updated registry is threaded forward after every
    accepted slash — this forward threading is the multi-transition core that
    single-shot mining lacks. Rules apply BOTH fresh and replayed evidence."""

    def __init__(self) -> None:
        super().__init__()
        # Build the initial two-subject registry. subject_id is taken from the
        # pre-built evidence pools so the packets actually match the bonds.
        entries = []
        self.bonded: dict[str, int] = {}
        self.subject_id: dict[str, str] = {}
        for key, pool in _EVIDENCE_POOLS.items():
            sid = str(pool["packets"][0]["subject_id"])  # type: ignore[index]
            self.subject_id[key] = sid
            self.bonded[key] = BONDED_AMOUNT
            entries.append(
                {
                    "subject_id": sid,
                    "subject_kind": pool["subject_kind"],
                    "bonded_amount": BONDED_AMOUNT,
                    "slashed_amount": 0,
                    "slashable_until_height": 100,
                    "status": "active",
                    "processed_evidence_hashes": [],
                }
            )
        self.registry = build_bond_registry_v0(chain_id=CHAIN_ID, asset_id=ASSET_ID, entries=entries)
        # External shadow ledger (independent of the module's own bookkeeping).
        self.cumulative_slashed: dict[str, int] = {k: 0 for k in _EVIDENCE_POOLS}
        self.prev_entry_slashed: dict[str, int] = {k: 0 for k in _EVIDENCE_POOLS}
        # Track which evidence hashes we've ever applied (for replay rules) and
        # which the module has actually processed (accepted).
        self.applied_hashes: dict[str, set[str]] = {k: set() for k in _EVIDENCE_POOLS}
        self.accepted_hashes: dict[str, set[str]] = {k: set() for k in _EVIDENCE_POOLS}

    def _entry_for(self, subject_key: str) -> dict[str, object]:
        sid = self.subject_id[subject_key]
        for entry in self.registry["entries"]:
            if entry["subject_id"] == sid:
                return dict(entry)
        raise AssertionError(f"subject {subject_key} vanished from registry")

    def _check_subject(self, subject_key: str) -> None:
        entry = self._entry_for(subject_key)
        assert_cumulative_slash_safe(
            subject_key=subject_key,
            bonded=self.bonded[subject_key],
            cumulative_slashed=self.cumulative_slashed[subject_key],
            entry_slashed=int(entry["slashed_amount"]),
            prev_entry_slashed=self.prev_entry_slashed[subject_key],
            entry_status=str(entry["status"]),
        )
        self.prev_entry_slashed[subject_key] = int(entry["slashed_amount"])

    def _apply(self, subject_key: str, evidence: dict[str, object], *, is_replay: bool) -> None:
        _pool = _EVIDENCE_POOLS[subject_key]
        policy = _POLICIES[subject_key]
        ev_hash = str(evidence["evidence_hash"])
        self.applied_hashes[subject_key].add(ev_hash)
        before_slashed = int(self._entry_for(subject_key)["slashed_amount"])
        try:
            transition = apply_bonded_slashing_v0(
                evidence=evidence, bond_registry=self.registry, policy=policy
            )
        except (ValueError, TypeError):
            # Rejected. Fail-closed contract: a reject is a strict no-op — the
            # threaded registry must be UNCHANGED (no partial slash on reject).
            after_slashed = int(self._entry_for(subject_key)["slashed_amount"])
            assert after_slashed == before_slashed, (
                f"REJECT-MUTATED-STATE: subject {subject_key} slashed changed "
                f"{before_slashed}->{after_slashed} on a rejected slash"
            )
            if is_replay and ev_hash in self.accepted_hashes[subject_key]:
                # A replay of an already-processed hash MUST reject (no double-slash)
                # — which it did. Good. Nothing else to assert.
                pass
            return

        # Accepted. Thread the updated registry forward (the multi-transition step).
        receipt = transition["receipt"]
        self.registry = transition["bond_registry"]
        slash_amount = int(receipt["slash_amount"])
        assert slash_amount > 0, f"accepted zero/negative slash amount {slash_amount}"
        assert before_slashed < self.bonded[subject_key], (
            f"ACCEPTED AFTER DEPLETION: subject {subject_key} accepted evidence "
            f"with slashed_amount already {before_slashed}"
        )
        assert before_slashed + slash_amount <= self.bonded[subject_key], (
            f"OVER-SLASH: subject {subject_key} accepted slash {slash_amount} "
            f"from {before_slashed}, exceeding bond {self.bonded[subject_key]}"
        )

        # A replay of an ALREADY-ACCEPTED hash must NEVER be accepted again.
        assert not (is_replay and ev_hash in self.accepted_hashes[subject_key]), (
            f"DOUBLE-SLASH VIA REPLAY: subject {subject_key} re-accepted already-"
            f"processed evidence {ev_hash[:18]} for another {slash_amount} slash"
        )
        self.accepted_hashes[subject_key].add(ev_hash)
        self.cumulative_slashed[subject_key] += slash_amount

        # The threaded registry must always re-validate (hash binding intact).
        validate_bond_registry_v0(self.registry)
        # The processed-hash set must now contain this evidence (provenance).
        entry = self._entry_for(subject_key)
        assert ev_hash in entry["processed_evidence_hashes"], (
            f"PROVENANCE: accepted evidence {ev_hash[:18]} not recorded in "
            f"subject {subject_key} processed_evidence_hashes"
        )
        assert set(entry["processed_evidence_hashes"]) == self.accepted_hashes[subject_key], (
            f"PROCESSED-HASH DRIFT: subject {subject_key} registry hashes "
            f"{entry['processed_evidence_hashes']} != accepted hashes "
            f"{sorted(self.accepted_hashes[subject_key])}"
        )
        self._check_subject(subject_key)

    @rule(variant=st.integers(min_value=0, max_value=_POOL_SIZE - 1))
    def fresh_checkpoint_slash(self, variant: int) -> None:
        ev = dict(_EVIDENCE_POOLS[_CHECKPOINT_SUBJECT]["packets"][variant])  # type: ignore[index]
        is_replay = str(ev["evidence_hash"]) in self.applied_hashes[_CHECKPOINT_SUBJECT]
        self._apply(_CHECKPOINT_SUBJECT, ev, is_replay=is_replay)

    @rule(variant=st.integers(min_value=0, max_value=_POOL_SIZE - 1))
    def fresh_watcher_slash(self, variant: int) -> None:
        ev = dict(_EVIDENCE_POOLS[_WATCHER_SUBJECT]["packets"][variant])  # type: ignore[index]
        is_replay = str(ev["evidence_hash"]) in self.applied_hashes[_WATCHER_SUBJECT]
        self._apply(_WATCHER_SUBJECT, ev, is_replay=is_replay)

    @precondition(lambda self: bool(self.accepted_hashes[_CHECKPOINT_SUBJECT]))
    @rule(data=st.data())
    def replay_processed_checkpoint(self, data) -> None:
        """Explicitly REPLAY an already-accepted checkpoint evidence hash. This is
        the direct double-slash-via-replay attempt: it must reject (strict no-op).
        """
        processed = sorted(self.accepted_hashes[_CHECKPOINT_SUBJECT])
        target = data.draw(st.sampled_from(processed))
        ev = next(
            dict(p)
            for p in _EVIDENCE_POOLS[_CHECKPOINT_SUBJECT]["packets"]  # type: ignore[union-attr]
            if str(p["evidence_hash"]) == target
        )
        self._apply(_CHECKPOINT_SUBJECT, ev, is_replay=True)

    @precondition(lambda self: bool(self.accepted_hashes[_WATCHER_SUBJECT]))
    @rule(data=st.data())
    def replay_processed_watcher(self, data) -> None:
        processed = sorted(self.accepted_hashes[_WATCHER_SUBJECT])
        target = data.draw(st.sampled_from(processed))
        ev = next(
            dict(p)
            for p in _EVIDENCE_POOLS[_WATCHER_SUBJECT]["packets"]  # type: ignore[union-attr]
            if str(p["evidence_hash"]) == target
        )
        self._apply(_WATCHER_SUBJECT, ev, is_replay=True)

    @invariant()
    def cumulative_slash_within_bond(self) -> None:
        for key in _EVIDENCE_POOLS:
            entry = self._entry_for(key)
            assert_cumulative_slash_safe(
                subject_key=key,
                bonded=self.bonded[key],
                cumulative_slashed=self.cumulative_slashed[key],
                entry_slashed=int(entry["slashed_amount"]),
                # use <= current as the monotonic floor (already advanced in steps)
                prev_entry_slashed=min(
                    self.prev_entry_slashed[key], int(entry["slashed_amount"])
                ),
                entry_status=str(entry["status"]),
            )

    @invariant()
    def registry_always_valid(self) -> None:
        validate_bond_registry_v0(self.registry)


# =========================================================================== #
# B. Dynamic-peer multi-round admission stateful machine.
# =========================================================================== #
NETWORK_ID = "zeno-testnet"
PEER_CHECK_SCHEMA = "zenodex.zeno_ledger.node_peer_check_report.v0"

# A bounded URL vocabulary so successive rounds overlap (re-admitting existing
# peers => admitted=[]) AND introduce new peers (set grows toward the cap). The
# pool is larger than the cap so unbounded-growth would be detectable.
_PEER_VOCAB = [f"http://peer{i}.example" for i in range(12)]
PEER_CAP = 8


def _peer_check_report(candidate_urls: list[str]) -> dict[str, object]:
    return {
        "schema": PEER_CHECK_SCHEMA,
        "network_id": NETWORK_ID,
        "chain_id": CHAIN_ID,
        "ok": True,
        "peers": [{"peer_url": url, "ok": True} for url in candidate_urls],
    }


class DynamicPeerMachine(RuleBasedStateMachine):
    """Drives REPEATED build_dynamic_peer_admission_v0 rounds, feeding each round's
    final_peer_urls forward as the next round's current_peer_urls. Every round
    uses a freshly-sampled candidate. Single-shot mining folds once; this folds
    once per @rule step, exercising multi-round accumulation toward the cap."""

    def __init__(self) -> None:
        super().__init__()
        self.current: list[str] = []
        self.round_index = 0

    @rule(
        raw_candidate=st.lists(st.sampled_from(_PEER_VOCAB), min_size=1, max_size=5),
        with_trailing_slash=st.booleans(),
    )
    def admit_round(self, raw_candidate: list[str], with_trailing_slash: bool) -> None:
        # Optionally append a trailing-slash variant of an existing url to exercise
        # cross-round canonical dedup (it must collapse, never grow the set twice).
        candidate_input = list(raw_candidate)
        if with_trailing_slash and self.current:
            candidate_input.append(self.current[0] + "/")
        candidate = peers.build_dynamic_peer_candidate_v0(
            network_id=NETWORK_ID,
            chain_id=CHAIN_ID,
            source_node_id="source-node",
            source_peer_url="http://source.example",
            candidate_peer_urls=candidate_input,
            observed_at_height=self.round_index + 1,
        )
        pcr = _peer_check_report(candidate["candidate_peer_urls"])
        prev_final = list(self.current)
        try:
            admission = peers.build_dynamic_peer_admission_v0(
                current_peer_urls=self.current,
                candidate=candidate,
                peer_check_report=pcr,
                max_peer_count=PEER_CAP,
            )
        except (ValueError, TypeError):
            # Admitting would exceed the cap (or another shape reject). Fail-closed:
            # the peer set must be UNCHANGED — no partial / over-cap admission.
            assert self.current == prev_final, (
                f"REJECT-MUTATED-STATE: round {self.round_index} current set "
                f"changed on a rejected admission"
            )
            return

        new_final = list(admission["final_peer_urls"])
        self.round_index += 1
        assert_peer_round_safe(
            prev_final=prev_final, new_final=new_final, cap=PEER_CAP, round_index=self.round_index
        )
        admitted = list(admission["admitted_peer_urls"])
        candidate_urls = list(candidate["candidate_peer_urls"])
        assert_peer_admission_delta_safe(
            prev_final=prev_final,
            candidate_urls=candidate_urls,
            admitted=admitted,
            new_final=new_final,
            round_index=self.round_index,
        )
        # COUNT INTEGRITY across the round.
        assert admission["final_peer_count"] == len(new_final), "final_peer_count mismatch"
        assert admission["admitted_peer_count"] == len(admitted), "admitted_peer_count mismatch"
        assert admission["current_peer_count"] == len(prev_final), "current_peer_count mismatch"
        assert admission["candidate_peer_count"] == len(candidate_urls), "candidate_peer_count mismatch"
        # Thread the new final set forward (the multi-round step).
        self.current = new_final

    @invariant()
    def peer_set_bounded_and_distinct(self) -> None:
        assert len(self.current) <= PEER_CAP, (
            f"UNBOUNDED PEER SET (invariant): {len(self.current)} > {PEER_CAP}"
        )
        assert len(self.current) == len(set(self.current)), (
            f"DUPLICATE peer in threaded set: {self.current}"
        )


# --------------------------------------------------------------------------- #
# Run the machines with deep step counts and many examples (rung-2 settings).
# --------------------------------------------------------------------------- #
_STATEFUL_SETTINGS = settings(
    max_examples=250,
    stateful_step_count=20,
    deadline=None,
    suppress_health_check=[HealthCheck.too_slow, HealthCheck.data_too_large],
)


def test_bonded_slashing_sequence_has_no_double_slash_witness() -> None:
    run_state_machine_as_test(BondedSlashingMachine, settings=_STATEFUL_SETTINGS)


def test_dynamic_peer_rounds_have_no_unbounded_accumulation_witness() -> None:
    run_state_machine_as_test(DynamicPeerMachine, settings=_STATEFUL_SETTINGS)


def test_depleted_bond_rejects_fresh_evidence_without_state_change() -> None:
    """A subject that has already reached the full bonded amount must reject even
    fresh evidence. This pins the post-depletion fail-closed edge that a
    cumulative-only checker could miss if an implementation accepted zero-effect
    receipts after depletion."""
    evidence = _checkpoint_evidence(vset_label="cp", height=7, variant=0)
    registry = build_bond_registry_v0(
        chain_id=CHAIN_ID,
        asset_id=ASSET_ID,
        entries=[
            {
                "subject_id": evidence["subject_id"],
                "subject_kind": "validator_set",
                "bonded_amount": BONDED_AMOUNT,
                "slashed_amount": BONDED_AMOUNT,
                "slashable_until_height": 100,
                "status": "slashed",
                "processed_evidence_hashes": [],
            }
        ],
    )
    before = copy.deepcopy(registry)
    with pytest.raises(ValueError, match="not active"):
        apply_bonded_slashing_v0(
            evidence=evidence,
            bond_registry=registry,
            policy=_POLICIES[_CHECKPOINT_SUBJECT],
        )
    assert registry == before


# --------------------------------------------------------------------------- #
# TEETH / non-vacuity: plant forged sequence outcomes; the cross-run invariant
# checkers MUST raise. A BUGGY reference is intentionally embedded here ONLY to
# prove the checker has teeth (it never touches src/).
# --------------------------------------------------------------------------- #
def test_teeth_cumulative_slash_over_bond_raises() -> None:
    """Plant a forged sequence outcome where cumulative slashed exceeds the bond
    (the double-slash-via-replay disaster). The cumulative checker MUST raise."""
    with pytest.raises(AssertionError, match="DOUBLE-SLASH"):
        assert_cumulative_slash_safe(
            subject_key=_CHECKPOINT_SUBJECT,
            bonded=1_000,
            cumulative_slashed=1_100,  # 11 hits of 100 — one past depletion
            entry_slashed=1_100,
            prev_entry_slashed=1_000,
            entry_status="slashed",
        )


def test_teeth_resurrection_raises() -> None:
    """Plant a forged outcome where a subject's slashed_amount DROPS across the run
    (registry resurrection). The monotonicity checker MUST raise."""
    with pytest.raises(AssertionError, match="NON-MONOTONIC / RESURRECTION"):
        assert_cumulative_slash_safe(
            subject_key=_WATCHER_SUBJECT,
            bonded=1_000,
            cumulative_slashed=300,
            entry_slashed=300,
            prev_entry_slashed=500,  # was 500, dropped to 300 -> resurrection
            entry_status="active",
        )


def test_teeth_buggy_reference_double_slash_sequence_is_caught() -> None:
    """A BUGGY reference apply that IGNORES the processed-evidence-hash dedup (so
    replaying the same evidence slashes again) is run as a SEQUENCE. Tracking its
    cumulative against the bond, the checker MUST catch the over-slash. This proves
    the stateful mine would flag a real double-slash regression, not pass silently.

    NOTE: this BUGGY function is a local stand-in ONLY — src/ is never modified.
    """

    def buggy_apply_ignoring_replay(*, slashed_so_far: int, slash_amount: int) -> int:
        # A correct impl rejects once slashed_so_far + slash_amount > bond; this
        # buggy one just adds unconditionally (no dedup, no available-bond check).
        return slashed_so_far + slash_amount

    bonded = 1_000
    cumulative = 0
    entry_slashed = 0
    # Replay the SAME 100-unit slash 12 times — a correct ledger caps at 10 hits.
    raised = False
    for _ in range(12):
        entry_slashed = buggy_apply_ignoring_replay(slashed_so_far=entry_slashed, slash_amount=100)
        cumulative += 100
        try:
            assert_cumulative_slash_safe(
                subject_key=_CHECKPOINT_SUBJECT,
                bonded=bonded,
                cumulative_slashed=cumulative,
                entry_slashed=entry_slashed,
                prev_entry_slashed=max(0, entry_slashed - 100),
                entry_status="slashed" if entry_slashed >= bonded else "active",
            )
        except AssertionError:
            raised = True
            break
    assert raised, "buggy double-slash sequence was NOT caught by the cumulative checker"


def test_teeth_unbounded_peer_accumulation_raises() -> None:
    """Plant a forged round outcome where the final set exceeds the cap (unbounded
    accumulation across rounds). The peer-round checker MUST raise."""
    with pytest.raises(AssertionError, match="UNBOUNDED PEER SET"):
        assert_peer_round_safe(
            prev_final=["http://peer0.example"],
            new_final=[f"http://peer{i}.example" for i in range(9)],  # 9 > cap 8
            cap=8,
            round_index=3,
        )


def test_teeth_peer_silent_drop_raises() -> None:
    """Plant a forged round outcome where a prior-round peer disappears (silent
    drop / non-monotonic registry). The peer-round checker MUST raise."""
    with pytest.raises(AssertionError, match="SILENT DROP|PEER SET SHRANK"):
        assert_peer_round_safe(
            prev_final=["http://peer0.example", "http://peer1.example"],
            new_final=["http://peer1.example"],  # peer0 dropped
            cap=8,
            round_index=4,
        )


def test_teeth_peer_phantom_admission_delta_raises() -> None:
    """Plant a forged round outcome that admits a peer outside the candidate
    delta. The provenance checker must catch the phantom admission."""
    with pytest.raises(AssertionError, match="ADMISSION DELTA DRIFT"):
        assert_peer_admission_delta_safe(
            prev_final=["http://peer0.example"],
            candidate_urls=["http://peer0.example", "http://peer1.example"],
            admitted=["http://evil.example"],
            new_final=["http://peer0.example", "http://evil.example"],
            round_index=5,
        )
