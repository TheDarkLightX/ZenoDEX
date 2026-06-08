"""WS2 — trustless refuse-by-default client admission decision (the north-star core).

> "Trust the MATH, not the hosts. If the host must be honest, it has failed."

A trustless client does NOT believe a host's claimed ACCEPT. It independently decides
ACCEPT / REFUSE by checking that a REAL proof BINDS THE RIGHT STATEMENT, fail-closed:
validity is a *precondition of acceptance*, not something the host asserts.

This module is the pure functional CORE of that decision. The only impure dependency
— actually verifying a RISC0 receipt — is an injected port (`ReceiptVerifierPort`), so
the core stays deterministic and exhaustively testable. The procedure runs an ordered
list of gates (0..N); the FIRST failing gate returns REFUSE(stable_code) and performs
NO mutation (reject-is-no-op). ACCEPT is a positive conjunction: it is returned only
if EVERY gate passes.

Design provenance: synthesized by the WS2 design workflow (understand → 3-lens design
panel → 8-vector adversarial red-team → synthesis) and grounded against the real Rust
journal structs (`zk/state_proof_risc0/shared/src/{surfaces,clob}.rs`) and the
consensus-semantics contract (`config/semantics/zenodex_consensus_contract_v1.json`).

NON-TRUST CLAUSE (load-bearing): no field ASSERTED by the host is ever an ACCEPT input.
`host_response.ok / proof_status / status / production_security_claim / is_final /
promotion_ready / artifact_binding_complete`, and the proof/journal's own claimed
image_id/chain_id, are UNTRUSTED HINTS only. The client-shipped pinned registry + the
client-trusted contract are the only trusted inputs. (Directly closes the fake-green
trap: `proof_verifier.py` only reads `ok`, never `production_security_claim`.)

This is a CLIENT-side reference policy. It does NOT edit the deployed admission path
(`orderbook_api.py`), the JS client, or the SDK; those mirror this canonical policy.

What this does NOT claim: liveness (an honest client must still be able to make
progress — see `head_advance`), oracle honesty, data availability, or that the proven
state is economically desirable. It proves only: a real proof, for THIS operation, at
or above the required claim level, bound to the client's head and pins.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Any, Callable, Mapping, Optional, Protocol, Sequence


# --------------------------------------------------------------------------- #
# Stable reject taxonomy (consensus behaviour: codes are part of the contract)
# --------------------------------------------------------------------------- #
class RefuseCode(str, Enum):
    UNMAPPED_OPERATION = "REFUSE_UNMAPPED_OPERATION"
    NO_PROOF = "REFUSE_NO_PROOF"
    VERIFIER_NOT_PINNED = "REFUSE_VERIFIER_NOT_PINNED"
    RECEIPT_VERIFY_FAILED = "REFUSE_RECEIPT_VERIFY_FAILED"
    PROOF_TYPE_MISMATCH = "REFUSE_PROOF_TYPE_MISMATCH"
    IMAGE_ID_MISMATCH = "REFUSE_IMAGE_ID_MISMATCH"
    CHAIN_ID_MISMATCH = "REFUSE_CHAIN_ID_MISMATCH"
    PRESTATE_UNBOUND = "REFUSE_PRESTATE_UNBOUND"
    PRESTATE_MISMATCH = "REFUSE_PRESTATE_MISMATCH"
    OPERATION_MISMATCH = "REFUSE_OPERATION_MISMATCH"
    BINDING_INCOMPLETE_OR_NULL = "REFUSE_BINDING_INCOMPLETE_OR_NULL"
    BINDING_MISMATCH = "REFUSE_BINDING_MISMATCH"
    CLAIM_TOO_WEAK = "REFUSE_CLAIM_TOO_WEAK"
    CLAIM_OVERCLAIM = "REFUSE_CLAIM_OVERCLAIM"
    ADMISSION_NOT_PROOF_GATED = "REFUSE_ADMISSION_NOT_PROOF_GATED"


class VerifyStatus(str, Enum):
    """Outcome of the injected receipt verifier. Anything not VERIFIED fails closed."""

    VERIFIED = "verified"
    FAILED = "failed"
    UNKNOWN = "unknown"
    TIMEOUT = "timeout"
    ERROR = "error"


# --------------------------------------------------------------------------- #
# Domain types (frozen; parse at the boundary into these)
# --------------------------------------------------------------------------- #
@dataclass(frozen=True)
class VerifierIdentity:
    """The blessed verifier the client is willing to run (pinned, not env-overridable)."""

    expected_cmd_hash: str
    binary_path: str  # MUST be absolute
    allow_path_lookup: bool = False  # MUST be False (no PATH-resolved verifier)


@dataclass(frozen=True)
class OperationPins:
    """Client-shipped pins for a (surface, operation). The trust root; never host-supplied."""

    surface: str
    operation: str
    pinned_image_id: tuple[int, ...]  # RISC0 image id [u32; 8]
    pinned_proof_type: str
    pinned_chain_id: str
    blessed_verifier: VerifierIdentity
    required_journal_fields: tuple[str, ...]  # CLOSED set, parity-tested vs the Rust struct
    expected_static: Mapping[str, Any]  # client-pinned expected values (rule hashes, policy)
    recomputed_fields: tuple[str, ...]  # fields whose expected value comes from the rebind
    cross_field_equal: tuple[tuple[str, str], ...]  # (field, must_equal_other_journal_field)
    head_equal_fields: tuple[str, ...]  # fields that must equal the client head when pre present
    claim_level: str  # the operation's ACTUAL contracted claim level
    ceiling_level: str  # max allowed claim level (overclaim guard)
    admission_threshold_level: str  # min level for live admissibility
    # Client-pinned ALLOW-LIST of deployed admission-binding statuses that mean "the
    # deployed admission actually requires THIS proof". Anything else -- including None,
    # unknown/typo, or a not_bound status -- fails closed. Empty () = no op admissible
    # yet (the honest current state until Stage 3 wires proof-gated admission).
    admission_proof_gated_statuses: tuple[str, ...] = ()


@dataclass(frozen=True)
class PinnedRegistry:
    by_op: Mapping[tuple[str, str], OperationPins]

    def get(self, surface: str, operation: str) -> Optional[OperationPins]:
        return self.by_op.get((surface, operation))


@dataclass(frozen=True)
class ConsensusContract:
    """Typed, fail-closed view over zenodex_consensus_contract_v1.json."""

    claim_levels_order: tuple[str, ...]  # the total order (weakest..strongest)
    required_level_by_op: Mapping[tuple[str, str], str]
    admission_binding_status_by_op: Mapping[tuple[str, str], Optional[str]]
    # proof_type -> claim level, built from operations[*].guest.{proof_type,
    # live_equivalence_claim_level}. The INDEPENDENT lookup that makes the gate-10
    # claim-level comparison non-tautological (keyed on the verified proof_type, not on
    # a hand-authored registry field).
    level_by_proof_type: Mapping[str, str]

    def rank(self, level: Optional[str]) -> Optional[int]:
        if level is None or level not in self.claim_levels_order:
            return None
        return self.claim_levels_order.index(level)

    def required_level(self, surface: str, operation: str) -> Optional[str]:
        return self.required_level_by_op.get((surface, operation))

    def admission_binding_status(self, surface: str, operation: str) -> Optional[str]:
        return self.admission_binding_status_by_op.get((surface, operation))

    def level_of_proof_type(self, proof_type: Optional[str]) -> Optional[str]:
        if proof_type is None:
            return None
        return self.level_by_proof_type.get(proof_type)


@dataclass(frozen=True)
class RequestedOperation:
    """Exactly the operation the client asked for. The trusted re-binding source."""

    surface: str
    operation: str
    fields: Mapping[str, Any]  # pubkey, asset, amount_e8, nonce, collateral_binding, run_epoch...


@dataclass(frozen=True)
class HeadRef:
    surface: str
    current_head: bytes  # the client's locally-maintained, retired-aware app head


@dataclass(frozen=True)
class HeadAdvanceObligation:
    """Emitted on ACCEPT; the imperative shell MUST apply it so a valid proof
    cannot be re-accepted (defeats stale replay; gives the pre==head check teeth)."""

    surface: str
    new_head: bytes
    retire_preroot: bytes


@dataclass(frozen=True)
class ReceiptVerifyResult:
    status: VerifyStatus
    journal: Optional[Mapping[str, Any]]  # parsed ONLY when status is VERIFIED
    error: Optional[str] = None


class ReceiptVerifierPort(Protocol):
    """The only impure dependency. An implementation MUST:
      (a) check the blessed verifier identity (cmd_hash + absolute binary, no PATH/env
          override) BEFORE running;
      (b) perform a REAL cryptographic receipt.verify against the CLIENT-pinned
          image_id (never the proof's claimed image id);
      (c) return UNKNOWN/TIMEOUT/ERROR distinctly (all fail closed);
      (d) never read/return production_security_claim or any host-asserted ok.
    It replaces trust in `SubprocessProofVerifier.verify`'s `(ok, None)` tuple."""

    def verify_receipt(
        self,
        proof_bytes: bytes,
        pinned_image_id: tuple[int, ...],
        *,
        blessed_verifier: VerifierIdentity,
    ) -> ReceiptVerifyResult: ...


# Client-side canonical re-encoder of the requested operation -> binding hashes
# (operation_hash + perps collateral/oracle binding hashes). Mirrors the guest's
# canonical encoders (canonical.py); parity-tested separately. Injected as a port so
# the decision core stays pure.
RebindFn = Callable[[RequestedOperation], Mapping[str, bytes]]


@dataclass(frozen=True)
class AdmissionDecision:
    accepted: bool
    claim_level: Optional[str]
    refuse_code: Optional[RefuseCode]
    head_advance: Optional[HeadAdvanceObligation]
    gate_results: Mapping[str, bool]
    tripwire: Optional[str] = None


# --------------------------------------------------------------------------- #
# Helpers (small, pure)
# --------------------------------------------------------------------------- #
_HOST_ASSERTED_FIELDS = (
    "ok",
    "proof_status",
    "status",
    "production_security_claim",
    "is_final",
    "promotion_ready",
    "artifact_binding_complete",
    "latest_proven_height",
)


def _extract_proof_bytes(host_response: Mapping[str, Any]) -> Optional[bytes]:
    """Pull raw proof material from the host response. Host-asserted status fields
    are deliberately NOT consulted."""
    raw = host_response.get("zk_proof")
    if raw is None:
        raw = host_response.get("proof")
    if raw is None:
        return None
    if isinstance(raw, (bytes, bytearray)):
        return bytes(raw) or None
    return None


def _is_present(value: Any) -> bool:
    """A binding value counts as present only if non-None and non-empty."""
    if value is None:
        return False
    if isinstance(value, (bytes, bytearray, str, tuple, list)) and len(value) == 0:
        return False
    return True


def _all_zero_image_id(image_id: Any) -> bool:
    if not isinstance(image_id, (tuple, list)) or len(image_id) == 0:
        return True
    return all(x == 0 for x in image_id)


# --------------------------------------------------------------------------- #
# The decision procedure
# --------------------------------------------------------------------------- #
def decide_admission(
    surface: str,
    operation: str,
    host_response: Mapping[str, Any],
    requested_operation: RequestedOperation,
    client_head: HeadRef,
    *,
    registry: PinnedRegistry,
    contract: ConsensusContract,
    verifier: ReceiptVerifierPort,
    rebind: RebindFn,
) -> AdmissionDecision:
    """Pure, fail-closed ACCEPT/REFUSE decision. First failing gate wins; no mutation.

    Required = True is a client constant: there is no env/request short-circuit that
    accepts the unproven. Returns ACCEPT only on the positive conjunction of all gates,
    carrying the operation's ACTUAL claim level + a HeadAdvanceObligation the shell
    must apply.
    """
    gate_results: dict[str, bool] = {}

    def refuse(code: RefuseCode, gate: str) -> AdmissionDecision:
        gate_results[gate] = False
        return AdmissionDecision(
            accepted=False,
            claim_level=None,
            refuse_code=code,
            head_advance=None,
            gate_results=gate_results,
        )

    def passed(gate: str) -> None:
        gate_results[gate] = True

    # Gate 0 — resolve client-trusted pins + contract row (reads NOTHING from host).
    # Identity consistency: every (surface, operation) the caller supplies must agree, or
    # we cannot establish a coherent trust root -> fail closed (no caller-discipline trust).
    if (
        requested_operation.surface != surface
        or requested_operation.operation != operation
        or client_head.surface != surface
    ):
        return refuse(RefuseCode.UNMAPPED_OPERATION, "g0_resolve_pins")
    pins = registry.get(surface, operation)
    required_level = contract.required_level(surface, operation)
    if pins is None or required_level is None:
        return refuse(RefuseCode.UNMAPPED_OPERATION, "g0_resolve_pins")
    if pins.surface != surface or pins.operation != operation:
        return refuse(RefuseCode.UNMAPPED_OPERATION, "g0_resolve_pins")
    if not pins.required_journal_fields:
        # An empty/incomplete required-field schema would make gate 9 vacuously pass.
        return refuse(RefuseCode.UNMAPPED_OPERATION, "g0_resolve_pins")
    if (
        contract.rank(required_level) is None
        or contract.rank(pins.claim_level) is None
        or contract.rank(pins.ceiling_level) is None
        or contract.rank(pins.admission_threshold_level) is None
    ):
        return refuse(RefuseCode.UNMAPPED_OPERATION, "g0_resolve_pins")
    # Registry consistency: the hand-authored pins.claim_level MUST equal the contract's
    # independent proof_type->level for the pinned proof_type. Otherwise the registry and
    # the contract disagree about what the pinned proof demonstrates -> fail closed.
    if contract.level_of_proof_type(pins.pinned_proof_type) != pins.claim_level:
        return refuse(RefuseCode.UNMAPPED_OPERATION, "g0_resolve_pins")
    passed("g0_resolve_pins")

    # Gate 1 — proof present (host-independent; do not read host-asserted status).
    proof_bytes = _extract_proof_bytes(host_response)
    if proof_bytes is None:
        return refuse(RefuseCode.NO_PROOF, "g1_proof_present")
    passed("g1_proof_present")

    # Gate 2 — verifier identity pin well-formed (no PATH lookup, absolute binary).
    bv = pins.blessed_verifier
    if bv.allow_path_lookup or not bv.binary_path.startswith("/") or not bv.expected_cmd_hash:
        return refuse(RefuseCode.VERIFIER_NOT_PINNED, "g2_verifier_pinned")
    passed("g2_verifier_pinned")

    # Gate 3 — REAL STARK verify against the CLIENT-pinned image id (never the proof's).
    # The journal is fabricated bytes until this passes.
    result = verifier.verify_receipt(proof_bytes, pins.pinned_image_id, blessed_verifier=bv)
    if result.status != VerifyStatus.VERIFIED or result.journal is None:
        return refuse(RefuseCode.RECEIPT_VERIFY_FAILED, "g3_receipt_verify")
    journal = result.journal
    passed("g3_receipt_verify")

    # Gate 4 — proof_type exact match (only unforgeable lane/surface discriminator).
    if journal.get("proof_type") != pins.pinned_proof_type:
        return refuse(RefuseCode.PROOF_TYPE_MISMATCH, "g4_proof_type")
    passed("g4_proof_type")

    # Gate 5 — image id echo: non-zero AND == pin (defense in depth; never replaces g3).
    journal_image = journal.get("risc0_image_id")
    if not isinstance(journal_image, (tuple, list)) or _all_zero_image_id(journal_image):
        return refuse(RefuseCode.IMAGE_ID_MISMATCH, "g5_image_id_echo")
    if tuple(journal_image) != tuple(pins.pinned_image_id):
        return refuse(RefuseCode.IMAGE_ID_MISMATCH, "g5_image_id_echo")
    passed("g5_image_id_echo")

    # Gate 6 — chain id pinned host-independently (blocks cross-chain replay).
    chain_id = journal.get("chain_id")
    if not _is_present(chain_id) or chain_id != pins.pinned_chain_id:
        return refuse(RefuseCode.CHAIN_ID_MISMATCH, "g6_chain_id")
    passed("g6_chain_id")

    # Gate 7 — pre-state bound to head: present-flag FIRST, then equality.
    # The guest skips the pre-root binding when present==False yet echoes the
    # attacker-supplied pre_app_hash (surfaces.rs:331/422), so the flag is load-bearing.
    if journal.get("pre_app_hash_present") is not True:
        return refuse(RefuseCode.PRESTATE_UNBOUND, "g7_prestate")
    if journal.get("pre_app_hash") != client_head.current_head:
        return refuse(RefuseCode.PRESTATE_MISMATCH, "g7_prestate")
    passed("g7_prestate")

    # Gate 8 — operation re-binding: recompute from the operation the client REQUESTED
    # (varies with amount/nonce; defeats replay of a cheap-op proof for an expensive op).
    recomputed = rebind(requested_operation)
    if not _is_present(recomputed.get("operation_hash")):
        return refuse(RefuseCode.OPERATION_MISMATCH, "g8_operation_rebind")
    if journal.get("operation_hash") != recomputed["operation_hash"]:
        return refuse(RefuseCode.OPERATION_MISMATCH, "g8_operation_rebind")
    passed("g8_operation_rebind")

    # Gate 9 — complete bindings over the CLOSED required field set: present-and-non-null
    # BEFORE equality, for EACH field. Drive off the closed set, not an open supplied map.
    for fieldname in pins.required_journal_fields:
        expected = _expected_binding_value(
            fieldname, pins=pins, recomputed=recomputed, journal=journal, head=client_head
        )
        if not _is_present(expected):
            return refuse(RefuseCode.BINDING_INCOMPLETE_OR_NULL, "g9_complete_bindings")
        actual = journal.get(fieldname)
        if not _is_present(actual):
            return refuse(RefuseCode.BINDING_INCOMPLETE_OR_NULL, "g9_complete_bindings")
        if actual != expected:
            return refuse(RefuseCode.BINDING_MISMATCH, "g9_complete_bindings")
    passed("g9_complete_bindings")

    # Gate 10 — claim level floor + ceiling, via TWO INDEPENDENT lookups (non-tautological):
    #   demonstrated := level_of_proof_type(VERIFIED journal.proof_type)  [keyed on the proof]
    #   required     := required_level(requested operation)              [keyed on the request]
    # Different keys -> genuinely independent (not a re-read of one hand-authored field).
    demonstrated_level = contract.level_of_proof_type(journal.get("proof_type"))
    demonstrated_rank = contract.rank(demonstrated_level)
    required_rank = contract.rank(required_level)  # from the requested operation
    ceiling_rank = contract.rank(pins.ceiling_level)
    if demonstrated_rank is None or required_rank is None or ceiling_rank is None:
        return refuse(RefuseCode.CLAIM_TOO_WEAK, "g10_claim_level")
    if demonstrated_rank < required_rank:
        return refuse(RefuseCode.CLAIM_TOO_WEAK, "g10_claim_level")
    if demonstrated_rank > ceiling_rank:
        return refuse(RefuseCode.CLAIM_OVERCLAIM, "g10_claim_level")
    passed("g10_claim_level")

    # Gate 11 — admission threshold + proof-gating. A genuinely-verified core_equivalent
    # proof for a Stage-0 (not-proof-gated) op is correct-but-NOT-admissible.
    threshold_rank = contract.rank(pins.admission_threshold_level)
    if threshold_rank is None or required_rank < threshold_rank:
        return refuse(RefuseCode.ADMISSION_NOT_PROOF_GATED, "g11_admission_gated")
    # Allow-list, fail-closed: admit ONLY if the deployed admission is a KNOWN
    # proof-gated status. Missing (None), unknown/typo, and any not_bound status all
    # refuse -- never trust an unrecognised status as admissible.
    binding_status = contract.admission_binding_status(surface, operation)
    if binding_status is None or binding_status not in pins.admission_proof_gated_statuses:
        return refuse(RefuseCode.ADMISSION_NOT_PROOF_GATED, "g11_admission_gated")
    passed("g11_admission_gated")

    # Gate 12 — ACCEPT (positive conjunction). Emit the head-advance obligation.
    post = journal.get("post_app_hash")
    if not isinstance(post, bytes) or len(post) == 0:
        # post must exist (as bytes) to advance the head; own gate key so the trace
        # stays clean (do not overwrite the already-passed g9 result).
        return refuse(RefuseCode.BINDING_INCOMPLETE_OR_NULL, "g12_post_present")
    passed("g12_accept")

    tripwire = _status_label_tripwire(host_response)
    return AdmissionDecision(
        accepted=True,
        claim_level=pins.claim_level,
        refuse_code=None,
        head_advance=HeadAdvanceObligation(
            surface=surface,
            new_head=post,
            retire_preroot=client_head.current_head,
        ),
        gate_results=gate_results,
        tripwire=tripwire,
    )


def _expected_binding_value(
    fieldname: str,
    *,
    pins: OperationPins,
    recomputed: Mapping[str, bytes],
    journal: Mapping[str, Any],
    head: HeadRef,
) -> Any:
    """Resolve the client-trusted expected value for a required journal field.

    Sources, in precedence: client-pinned static (rule hashes / authority policy) >
    recomputed-from-request (operation/collateral/oracle hashes) > cross-field
    consistency (e.g. post_book_root == post_app_hash) > head-bound (e.g.
    pre_book_root == client head). Returns None if no trusted source exists, which the
    caller treats as REFUSE_BINDING_INCOMPLETE_OR_NULL (fail-closed, never trust the
    host value for an unsourced field)."""
    if fieldname in pins.expected_static:
        return pins.expected_static[fieldname]
    if fieldname in pins.recomputed_fields:
        return recomputed.get(fieldname)
    for src, other in pins.cross_field_equal:
        if src == fieldname:
            return journal.get(other)
    if fieldname in pins.head_equal_fields:
        return head.current_head
    return None


def _status_label_tripwire(host_response: Mapping[str, Any]) -> Optional[str]:
    """Non-gating consistency tripwire: if the host loudly claims verified/final while
    we are about to ACCEPT on our own evidence, that is fine; if it claims NOT verified,
    log the discrepancy. The host label NEVER drives the decision."""
    for field in _HOST_ASSERTED_FIELDS:
        if field in host_response:
            return f"host_asserted_fields_ignored:{sorted(f for f in _HOST_ASSERTED_FIELDS if f in host_response)}"
    return None
