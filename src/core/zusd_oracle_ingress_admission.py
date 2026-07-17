"""Pure admission relation for zUSD oracle-sensitive ingress.

This kernel deliberately consumes normalized evidence-binding facts.  The
imperative shell is responsible for verifying external receipts and may set a
fact to ``True`` only after binding it to the exact action and staged pre-state.
The kernel owns the profile-specific *port* obligation matrix and returns its
complete ordered violation set without mutating protocol state.  Each port bit
is a conjunction of lower-level verifier obligations, whose individual failure
reasons are outside this abstraction.  This is not the complete F03 oracle FSM.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum

ZUSD_ORACLE_INGRESS_ADMISSION_NONCLAIMS = (
    "external_verifier_failure_detail",
    "oracle_truth_or_receipt_authenticity",
    "complete_f03_oracle_fsm",
    "python_shell_refinement_from_esso_alone",
)


class ZUSDOracleEvidenceProfile(str, Enum):
    """Versioned oracle-evidence policy committed with monetary state."""

    CONFIGURED_SIGNER_DEV_V0 = (
        "zenodex/zusd-oracle-evidence/configured-signer-dev-v0"
    )
    FINALIZED_O3_V1 = "zenodex/zusd-oracle-evidence/finalized-o3-v1"


class ZUSDOracleIngressAction(str, Enum):
    ADVANCE_EPOCH = "advance_epoch"
    BOOTSTRAP_ORACLE = "bootstrap_oracle"
    ORACLE_REPORT = "oracle_report"
    ORACLE_COMMIT = "oracle_commit"
    LIQUIDATE = "liquidate"
    MINT_ZUSD = "mint_zusd"


class ZUSDOracleIngressViolation(str, Enum):
    CONFIGURED_SENDER_REQUIRED = "configured_sender_required"
    FINALIZED_CONTEXT_REQUIRED = "finalized_context_required"
    AGGREGATE_PROPOSAL_REQUIRED = "aggregate_proposal_required"
    EXACT_PENDING_SNAPSHOT_REQUIRED = "exact_pending_snapshot_required"
    COMMITTED_ACTIVE_SNAPSHOT_REQUIRED = "committed_active_snapshot_required"
    CRITICAL_ACTION_AUTHORIZATION_REQUIRED = (
        "critical_action_authorization_required"
    )


@dataclass(frozen=True)
class ZUSDOracleIngressEvidence:
    """Normalized, action-bound evidence facts supplied by the shell."""

    configured_sender_bound: bool = False
    # Conjunction of F02 receipt authenticity, finality, and exact context.
    finalized_context_bound: bool = False
    # Conjunction of proposal authenticity, F01 profile/chain/asset/source-set
    # binding, positive/fresh price, monotone round, exact pre-state/sequence,
    # and unused source-nullifier position.
    aggregate_proposal_bound: bool = False
    # Conjunction of pending existence, exact root, freshness, expected
    # pre-state/sequence, and inherited authenticated proposal provenance.
    pending_snapshot_bound: bool = False
    # Conjunction of committed active-snapshot provenance, exact projection,
    # freshness, and expected context/root binding.
    committed_active_snapshot_bound: bool = False
    # Conjunction of the cataloged O3 receipt and exact consumer action,
    # pre-state, profile, query, value, freshness, and trusted-root binding.
    critical_action_authorization_bound: bool = False

    def __post_init__(self) -> None:
        for field_name in (
            "configured_sender_bound",
            "finalized_context_bound",
            "aggregate_proposal_bound",
            "pending_snapshot_bound",
            "committed_active_snapshot_bound",
            "critical_action_authorization_bound",
        ):
            if type(getattr(self, field_name)) is not bool:
                raise TypeError(f"{field_name} must be exactly bool")


@dataclass(frozen=True)
class ZUSDOracleIngressDecision:
    admitted: bool
    violations: tuple[ZUSDOracleIngressViolation, ...]

    def __post_init__(self) -> None:
        if type(self.admitted) is not bool:
            raise TypeError("admitted must be exactly bool")
        if type(self.violations) is not tuple:
            raise TypeError("violations must be exactly tuple")
        if any(type(item) is not ZUSDOracleIngressViolation for item in self.violations):
            raise TypeError("violations must contain exact violation values")
        if self.admitted != (len(self.violations) == 0):
            raise ValueError("admitted must be equivalent to empty violations")


_DEV_SIGNER_ACTIONS = frozenset(
    {
        ZUSDOracleIngressAction.ADVANCE_EPOCH,
        ZUSDOracleIngressAction.BOOTSTRAP_ORACLE,
        ZUSDOracleIngressAction.ORACLE_REPORT,
        ZUSDOracleIngressAction.ORACLE_COMMIT,
    }
)


def evaluate_zusd_oracle_ingress_admission(
    *,
    profile: ZUSDOracleEvidenceProfile,
    action: ZUSDOracleIngressAction,
    evidence: ZUSDOracleIngressEvidence,
) -> ZUSDOracleIngressDecision:
    """Return the lossless profile-specific *port-level* violation set."""

    if type(profile) is not ZUSDOracleEvidenceProfile:
        raise TypeError("profile must be exactly ZUSDOracleEvidenceProfile")
    if type(action) is not ZUSDOracleIngressAction:
        raise TypeError("action must be exactly ZUSDOracleIngressAction")
    if type(evidence) is not ZUSDOracleIngressEvidence:
        raise TypeError("evidence must be exactly ZUSDOracleIngressEvidence")

    violations: list[ZUSDOracleIngressViolation] = []
    if profile is ZUSDOracleEvidenceProfile.CONFIGURED_SIGNER_DEV_V0:
        if action in _DEV_SIGNER_ACTIONS and not evidence.configured_sender_bound:
            violations.append(
                ZUSDOracleIngressViolation.CONFIGURED_SENDER_REQUIRED
            )
    else:
        if not evidence.finalized_context_bound:
            violations.append(
                ZUSDOracleIngressViolation.FINALIZED_CONTEXT_REQUIRED
            )
        if action in {
            ZUSDOracleIngressAction.BOOTSTRAP_ORACLE,
            ZUSDOracleIngressAction.ORACLE_REPORT,
        }:
            if not evidence.aggregate_proposal_bound:
                violations.append(
                    ZUSDOracleIngressViolation.AGGREGATE_PROPOSAL_REQUIRED
                )
        if (
            action is ZUSDOracleIngressAction.ORACLE_COMMIT
            and not evidence.pending_snapshot_bound
        ):
            violations.append(
                ZUSDOracleIngressViolation.EXACT_PENDING_SNAPSHOT_REQUIRED
            )
        if action in {
            ZUSDOracleIngressAction.LIQUIDATE,
            ZUSDOracleIngressAction.MINT_ZUSD,
        }:
            if not evidence.committed_active_snapshot_bound:
                violations.append(
                    ZUSDOracleIngressViolation.COMMITTED_ACTIVE_SNAPSHOT_REQUIRED
                )
            if not evidence.critical_action_authorization_bound:
                violations.append(
                    ZUSDOracleIngressViolation.CRITICAL_ACTION_AUTHORIZATION_REQUIRED
                )

    ordered = tuple(violations)
    return ZUSDOracleIngressDecision(
        admitted=not ordered,
        violations=ordered,
    )
