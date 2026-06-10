"""WS2 imperative shell: the refuse-by-default loop around `decide_admission`.

The pure core emits a `HeadAdvanceObligation` on ACCEPT but cannot enforce it.
This shell is the enforcement: it owns the client's head, applies the obligation
ATOMICALLY under a lock (the anti-double-accept property), and never mutates on
REFUSE. `MultiHostAdmissionClient` adds the liveness half of the trust model:
hosts are interchangeable relays — a withholding or corrupting host is *routed
around*, never trusted harder.

What this shell does NOT provide (honesty): data-availability/ordering trust for
the INITIAL head (the caller supplies genesis or a checkpoint it already trusts),
oracle honesty, or economic desirability of the proven transition. It turns
"valid proof for the right statement" into "accepted, exactly once, in order".
"""

from __future__ import annotations

import threading
from dataclasses import dataclass
from typing import Any, Callable, Mapping, Optional, Sequence

from src.integration.client_admission_decision import (
    AdmissionDecision,
    ConsensusContract,
    HeadRef,
    PinnedRegistry,
    RebindFn,
    ReceiptVerifierPort,
    RefuseCode,
    RequestedOperation,
    decide_admission,
)

__all__ = [
    "ClientAdmissionLoop",
    "ClientAdmissionLoopError",
    "HostAttempt",
    "MultiHostAdmissionClient",
    "MultiHostOutcome",
]


class ClientAdmissionLoopError(ValueError):
    """Misconfigured shell (not a host-data condition): fail at construction."""


@dataclass(frozen=True)
class HostAttempt:
    """One host's outcome inside a multi-host admission round."""

    host_id: str
    accepted: bool
    refuse_code: Optional[RefuseCode]
    transport_error: Optional[str]


@dataclass(frozen=True)
class MultiHostOutcome:
    """ACCEPT from the first host whose response verifies; REFUSE only after
    every host failed. `attempts` is the full per-host audit trail."""

    accepted: bool
    decision: Optional[AdmissionDecision]
    served_by: Optional[str]
    attempts: tuple[HostAttempt, ...]


class ClientAdmissionLoop:
    """Single-surface refuse-by-default client loop.

    Holds the client head for `surface`, decides every host response through the
    pure core, and applies the head-advance obligation atomically. The lock spans
    decide+advance so two concurrent submissions of the same valid proof can
    never both ACCEPT (the second sees the advanced head and refuses at gate 7).
    """

    def __init__(
        self,
        surface: str,
        initial_head: bytes,
        *,
        registry: PinnedRegistry,
        contract: ConsensusContract,
        verifier_by_operation: Mapping[str, ReceiptVerifierPort],
        rebind_by_operation: Mapping[str, RebindFn],
    ) -> None:
        if type(surface) is not str or not surface:
            raise ClientAdmissionLoopError("surface must be a non-empty string")
        if type(initial_head) is not bytes or len(initial_head) == 0:
            raise ClientAdmissionLoopError("initial_head must be non-empty bytes")
        if not verifier_by_operation or not rebind_by_operation:
            raise ClientAdmissionLoopError("verifier and rebind maps must be non-empty")
        if set(verifier_by_operation.keys()) != set(rebind_by_operation.keys()):
            raise ClientAdmissionLoopError("verifier/rebind operation sets must match")
        self._surface = surface
        self._head = bytes(initial_head)
        self._retired: set[bytes] = set()
        self._registry = registry
        self._contract = contract
        self._verifier_by_operation = dict(verifier_by_operation)
        self._rebind_by_operation = dict(rebind_by_operation)
        self._lock = threading.Lock()

    @property
    def surface(self) -> str:
        return self._surface

    def current_head(self) -> bytes:
        with self._lock:
            return self._head

    def retired_roots(self) -> frozenset[bytes]:
        with self._lock:
            return frozenset(self._retired)

    def submit(
        self,
        operation: str,
        host_response: Mapping[str, Any],
        requested_fields: Mapping[str, Any],
    ) -> AdmissionDecision:
        """Decide one host response. ACCEPT advances the head atomically;
        REFUSE is a no-op (reject-is-no-op extends to the shell)."""
        verifier = self._verifier_by_operation.get(operation)
        rebind = self._rebind_by_operation.get(operation)
        if verifier is None or rebind is None:
            # No configured ports for this operation -> structurally unmapped.
            return decide_admission(
                self._surface,
                operation,
                host_response,
                RequestedOperation(surface=self._surface, operation=operation, fields={}),
                HeadRef(surface=self._surface, current_head=b""),
                registry=PinnedRegistry(by_op={}),
                contract=self._contract,
                verifier=_NeverVerifier(),
                rebind=lambda _op: {},
            )
        requested = RequestedOperation(
            surface=self._surface, operation=operation, fields=dict(requested_fields)
        )
        with self._lock:
            decision = decide_admission(
                self._surface,
                operation,
                host_response,
                requested,
                HeadRef(surface=self._surface, current_head=self._head),
                registry=self._registry,
                contract=self._contract,
                verifier=verifier,
                rebind=rebind,
            )
            if decision.accepted:
                obligation = decision.head_advance
                # The core guarantees these on ACCEPT; treat violation as a bug,
                # not a host condition.
                assert obligation is not None
                assert obligation.surface == self._surface
                assert obligation.retire_preroot == self._head
                # The core already rejects post == head (gate 12). The shell owns
                # the one invariant the pure core cannot see: advancing INTO an
                # already-retired root would re-open that root's consumed proof for
                # replay (a state cycle Hk -> ... -> Hk). Refuse fail-closed; do
                # not mutate the head or the retired set. Record the shell gate as
                # FAILED so the audit trace has a first-false gate for the refusal
                # (the core's results are all-true on this path).
                if obligation.new_head in self._retired:
                    shell_gates = dict(decision.gate_results)
                    shell_gates["g13_head_not_retired"] = False
                    return AdmissionDecision(
                        accepted=False,
                        claim_level=None,
                        refuse_code=RefuseCode.HEAD_NONPROGRESS,
                        head_advance=None,
                        gate_results=shell_gates,
                    )
                self._retired.add(obligation.retire_preroot)
                self._head = obligation.new_head
            return decision


class _NeverVerifier:
    """Port used only on unmapped operations; the empty registry refuses at
    gate 0 before any verify, but fail closed if it were ever reached."""

    def verify_receipt(self, proof_bytes: bytes, pinned_image_id, *, blessed_verifier):
        from src.integration.client_admission_decision import (
            ReceiptVerifyResult,
            VerifyStatus,
        )

        return ReceiptVerifyResult(
            status=VerifyStatus.ERROR, journal=None, error="no verifier configured"
        )


# A host port is (host_id, fetch). fetch performs the impure call to one host and
# returns its raw response; it may raise (treated as transport failure). The
# return is typed Any, not Mapping: a host is UNTRUSTED, so the shell must keep
# its non-Mapping defensive check live rather than assume a well-typed response.
HostFetch = Callable[[Mapping[str, Any]], Any]


class MultiHostAdmissionClient:
    """Liveness via multiplicity: ask hosts in order; the FIRST response that
    fully verifies is accepted; everything else is recorded and routed around.

    A host can WITHHOLD (we move on) but cannot CORRUPT (a wrong result carries
    no verifying proof, so it is refused and the next host is tried). No retry
    loop ever relaxes a gate; running out of hosts is a liveness failure, never
    an acceptance."""

    def __init__(self, loop: ClientAdmissionLoop, hosts: Sequence[tuple[str, HostFetch]]) -> None:
        if not hosts:
            raise ClientAdmissionLoopError("at least one host is required")
        seen: set[str] = set()
        for host_id, _fetch in hosts:
            if type(host_id) is not str or not host_id:
                raise ClientAdmissionLoopError("host ids must be non-empty strings")
            if host_id in seen:
                raise ClientAdmissionLoopError(f"duplicate host id {host_id!r}")
            seen.add(host_id)
        self._loop = loop
        self._hosts = list(hosts)

    def fetch_and_admit(
        self,
        operation: str,
        requested_fields: Mapping[str, Any],
        request: Mapping[str, Any],
    ) -> MultiHostOutcome:
        attempts: list[HostAttempt] = []
        for host_id, fetch in self._hosts:
            try:
                response = fetch(request)
            except Exception as exc:  # noqa: BLE001 - any transport fault = try next host
                attempts.append(
                    HostAttempt(
                        host_id=host_id,
                        accepted=False,
                        refuse_code=None,
                        transport_error=f"{type(exc).__name__}: {exc}",
                    )
                )
                continue
            if not isinstance(response, Mapping):
                attempts.append(
                    HostAttempt(
                        host_id=host_id,
                        accepted=False,
                        refuse_code=None,
                        transport_error="host returned a non-object response",
                    )
                )
                continue
            decision = self._loop.submit(operation, response, requested_fields)
            attempts.append(
                HostAttempt(
                    host_id=host_id,
                    accepted=decision.accepted,
                    refuse_code=decision.refuse_code,
                    transport_error=None,
                )
            )
            if decision.accepted:
                return MultiHostOutcome(
                    accepted=True,
                    decision=decision,
                    served_by=host_id,
                    attempts=tuple(attempts),
                )
        return MultiHostOutcome(
            accepted=False, decision=None, served_by=None, attempts=tuple(attempts)
        )
