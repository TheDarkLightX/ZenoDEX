"""TAU-CONSTITUTION v1 — client-re-runnable rule-of-law (pure functional core).

This module is the CONSTITUTION REGISTRY: it maps each settlement surface to
the governing Tau spec file and a canonical ``policy_hash``. The policy_hash is
designed to be bound into a settlement receipt so that a settlement is
inseparable from the rule that authorized it. A client can independently hash
the ``.tau`` file it downloaded and confirm it matches the rule that judged its
trade.

DESIGN NORTH STAR: trust the MATH, not the hosts. Validity is a precondition of
acceptance, enforced by the client. ``policy_hash`` binds the *exact bytes* of
the governing rule plus the parameters that determine the verdict (which output
stream is read, and which witness-encoding maps the trade onto the i1..i15
stream).

HONEST SCOPE OF WHAT THE SPOT RULE DECIDES (``swap_exact_in_v1.tau``):
The spot constitution proves an ADMISSION rule — bounds, slippage, and
reserve-transition consistency:

  * positivity of reserve_in, reserve_out, amount_in, amount_out;
  * ``fee_bps in [0, 10000]`` (range-checked only — see below);
  * ``amount_out >= min_amount_out`` (slippage);
  * ``reserve_out >= amount_out``;
  * ``new_reserve_in = reserve_in + amount_in`` (16-bit-limb, no-carry);
  * ``new_reserve_out = reserve_out - amount_out`` (16-bit-limb, no-borrow).

It does **NOT** verify that ``amount_out`` is the correct CPMM / fee-adjusted
price. ``fee_bps`` is range-checked but never used in a pricing formula. A
re-run reproduces "your trade obeyed the admission rule", NOT "your trade was
priced correctly". Pricing correctness (binding the richer fee-proof-gate
specs) is Phase 2 and explicitly out of v1 scope.

ADDITIONAL HONEST CAVEAT (limb arithmetic): the governing spec encodes the
32-bit reserve transition as two independent 16-bit limbs with no cross-limb
carry/borrow (see ``add_32`` / ``sub_32`` in the spec). It therefore only admits
transitions whose low 16-bit limb does not carry on add or borrow on subtract.
The Python mirror in :mod:`src.integration.tau_constitution_rerunner`
reproduces this limb-exact semantics so that the client's re-derivation matches
the literal rule, not an idealized full-integer version of it.

This module is pure: no IO, no clocks, no randomness. ``policy_hash`` values are
deterministic functions of the on-disk spec bytes and are computed once at
import time.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from enum import Enum
from pathlib import Path
from typing import Any, Mapping

# NOTE: importing hash_v0 from the integration layer is intentional. policy_hash
# is a ledger-domain commitment, so we reuse the SAME domain-separated hashing
# primitive the ZenoLedger body uses (no new hash primitive) for parity with the
# existing batch_cutoff (policy_id, policy_digest) precedent. The receipt-body
# hash below builds directly on src/state/canonical.py.
from ..integration.zeno_ledger_v0 import hash_v0
from ..state.canonical import (
    canonical_json_bytes,
    domain_sep_bytes,
    sha256_hex,
)

# ---------------------------------------------------------------------------
# Schema / domain constants
# ---------------------------------------------------------------------------

TAU_CONSTITUTION_SCHEMA_V1 = "zenodex/tau_constitution/v1"
TAU_CONSTITUTION_POLICY_HASH_DOMAIN = "tau_constitution_policy_v1"
TAU_CONSTITUTION_RECEIPT_SCHEMA = "zenodex/tau_constitution_receipt/v1"
TAU_CONSTITUTION_RECEIPT_HASH_DOMAIN = "zenodex.tau_constitution_receipt/v1"

# The ONLY scope a v1 constitution receipt may claim: the rule decides admission
# (bounds + slippage + reserve-transition consistency), NOT pricing correctness.
# Pinned so a receipt cannot overclaim a richer scope than the rule decides.
TAU_CONSTITUTION_DECIDED_SCOPE = "admission_only_not_pricing"

# The witness-encoding version is load-bearing: it pins the i1..i15 stream
# mapping (``build_swap_exact_in_v1_step``). Bump this if the encoding changes;
# the bump flows into policy_hash so an altered encoding produces a new hash.
SWAP_EXACT_IN_WITNESS_ENCODING_V1 = "swap_exact_in_v1/i1_i15/hi_lo_u32"

PROJECT_ROOT = Path(__file__).resolve().parents[2]
# REVIEW [B -> A-]: this module is covered by the functional-core
# no-float/no-true-division gate. Pathlib "/" joins are harmless at runtime, but
# they weaken that gate by requiring exceptions for the same AST operator that
# would catch numeric true division. Use joinpath so the policy has teeth.
TAU_SPECS_DIR = PROJECT_ROOT.joinpath("src", "tau_specs")
RECOMMENDED_SPECS_DIR = TAU_SPECS_DIR.joinpath("recommended")

_HEX_32_RE = re.compile(r"^0x[0-9a-f]{64}$")
_TOKEN_RE = re.compile(r"^[A-Za-z0-9_.:/-]{1,128}$")


class ConstitutionError(ValueError):
    """Raised for malformed registry construction (import-time integrity)."""


# ---------------------------------------------------------------------------
# Surface enum + registry entry
# ---------------------------------------------------------------------------


class SettlementSurface(Enum):
    """Settlement surfaces governed by a Tau constitution.

    Only ``SPOT_SWAP_EXACT_IN`` is wired end-to-end (witness builder +
    re-runner + receipt binding) in v1. All other surfaces are REGISTRY-ONLY:
    their spec is registered and a policy_hash is computed, but no re-runner
    witness adapter is shipped. A re-run attempt for those surfaces fails closed
    with the stable code ``rerunner_not_wired_v1``.
    """

    SPOT_SWAP_EXACT_IN = "spot_swap_exact_in"
    SPOT_SWAP_EXACT_OUT = "spot_swap_exact_out"
    ADD_LIQUIDITY = "add_liquidity"
    REMOVE_LIQUIDITY = "remove_liquidity"
    CREATE_POOL = "create_pool"


@dataclass(frozen=True)
class ConstitutionEntry:
    """A frozen registry entry binding a surface to its governing Tau rule.

    Attributes:
        surface: the settlement surface this rule governs.
        spec_id: the stable identifier of the governing spec.
        spec_path: absolute path to the ``.tau`` file whose RAW bytes are hashed.
        gate_output: the output stream that carries the verdict (e.g. ``o1``).
        witness_encoding_version: pins the i1..i15 stream mapping.
        wired_e2e: True only for surfaces with a re-runner witness adapter.
    """

    surface: SettlementSurface
    spec_id: str
    spec_path: Path
    gate_output: str
    witness_encoding_version: str
    wired_e2e: bool

    @property
    def surface_id(self) -> str:
        return self.surface.value


def _read_spec_bytes(spec_path: Path) -> bytes:
    """Read the RAW bytes of a governing spec file (the bytes a user downloads).

    We hash raw bytes (not normalized text) because that is what a user can most
    obviously reproduce: download the file, ``sha256`` it. The encoding is the
    file's on-disk bytes verbatim; no decoding/normalization is applied.
    """
    if not spec_path.exists() or not spec_path.is_file():
        raise ConstitutionError(f"governing spec not found: {spec_path}")
    data = spec_path.read_bytes()
    if len(data) == 0:
        raise ConstitutionError(f"governing spec is empty: {spec_path}")
    return data


def spec_bytes_sha256(spec_path: Path) -> str:
    """sha256 of the RAW ``.tau`` file bytes, as a 0x 32-byte hex string."""
    return sha256_hex(_read_spec_bytes(spec_path))


def _policy_hash_from_fields(
    *,
    surface_id: str,
    spec_id: str,
    gate_output: str,
    witness_encoding_version: str,
    spec_bytes_digest: str,
) -> str:
    """Canonical policy_hash over the binding fields.

    Factored out so tests can compute the hash over a *mutated* set of fields
    (e.g. a tampered spec digest, a different gate_output, or a bumped encoding
    version) and confirm the binding is real, not cosmetic.
    """
    if not _HEX_32_RE.fullmatch(spec_bytes_digest):
        raise ConstitutionError("spec_bytes_digest must be a 0x 32-byte hex string")
    return hash_v0(
        TAU_CONSTITUTION_POLICY_HASH_DOMAIN,
        {
            "schema": TAU_CONSTITUTION_SCHEMA_V1,
            "surface_id": surface_id,
            "spec_id": spec_id,
            "gate_output": gate_output,
            "witness_encoding_version": witness_encoding_version,
            "spec_bytes_sha256": spec_bytes_digest,
        },
    )


def constitution_policy_hash(entry: ConstitutionEntry) -> str:
    """Compute the canonical policy_hash for a registry entry.

    ``policy_hash = hash_v0('tau_constitution_policy_v1', {schema, surface_id,
    spec_id, gate_output, witness_encoding_version, spec_bytes_sha256})`` where
    ``spec_bytes_sha256`` is the sha256 of the RAW ``.tau`` file bytes.

    Changing one byte of the governing rule, the output stream read, or the
    witness-encoding version changes the policy_hash. This is the moat: the
    client hashes the file it downloaded and confirms it matches the rule that
    judged its trade.
    """
    if not isinstance(entry, ConstitutionEntry):
        raise TypeError("entry must be a ConstitutionEntry")
    return _policy_hash_from_fields(
        surface_id=entry.surface_id,
        spec_id=entry.spec_id,
        gate_output=entry.gate_output,
        witness_encoding_version=entry.witness_encoding_version,
        spec_bytes_digest=spec_bytes_sha256(entry.spec_path),
    )


# ---------------------------------------------------------------------------
# The registry
# ---------------------------------------------------------------------------


def _build_registry() -> dict[SettlementSurface, ConstitutionEntry]:
    """Build the v1 constitution registry. Validated at import time."""
    entries = [
        ConstitutionEntry(
            surface=SettlementSurface.SPOT_SWAP_EXACT_IN,
            spec_id="swap_exact_in_v1",
            spec_path=RECOMMENDED_SPECS_DIR.joinpath("swap_exact_in_v1.tau"),
            gate_output="o1",
            witness_encoding_version=SWAP_EXACT_IN_WITNESS_ENCODING_V1,
            wired_e2e=True,
        ),
        # Registry-only surfaces (v1): registered + policy_hash computed, but no
        # re-runner witness adapter shipped. Re-run attempts fail closed with
        # ``rerunner_not_wired_v1``.
        ConstitutionEntry(
            surface=SettlementSurface.SPOT_SWAP_EXACT_OUT,
            spec_id="swap_exact_out_v1",
            spec_path=RECOMMENDED_SPECS_DIR.joinpath("swap_exact_out_v1.tau"),
            gate_output="o1",
            witness_encoding_version="registry_only_v1",
            wired_e2e=False,
        ),
        ConstitutionEntry(
            surface=SettlementSurface.ADD_LIQUIDITY,
            spec_id="add_liquidity_apply_v1",
            spec_path=RECOMMENDED_SPECS_DIR.joinpath("add_liquidity_apply_v1.tau"),
            gate_output="o1",
            witness_encoding_version="registry_only_v1",
            wired_e2e=False,
        ),
        ConstitutionEntry(
            surface=SettlementSurface.REMOVE_LIQUIDITY,
            spec_id="remove_liquidity_apply_v1",
            spec_path=RECOMMENDED_SPECS_DIR.joinpath("remove_liquidity_apply_v1.tau"),
            gate_output="o1",
            witness_encoding_version="registry_only_v1",
            wired_e2e=False,
        ),
        ConstitutionEntry(
            surface=SettlementSurface.CREATE_POOL,
            spec_id="create_pool_apply_proof_gate_v1",
            spec_path=RECOMMENDED_SPECS_DIR.joinpath("create_pool_apply_proof_gate_v1.tau"),
            gate_output="o1",
            witness_encoding_version="registry_only_v1",
            wired_e2e=False,
        ),
    ]

    registry: dict[SettlementSurface, ConstitutionEntry] = {}
    for entry in entries:
        if entry.surface in registry:
            raise ConstitutionError(f"duplicate surface in registry: {entry.surface}")
        if not _TOKEN_RE.fullmatch(entry.spec_id):
            raise ConstitutionError(f"invalid spec_id token: {entry.spec_id!r}")
        if not re.fullmatch(r"o\d+", entry.gate_output):
            raise ConstitutionError(f"invalid gate_output: {entry.gate_output!r}")
        # Fail closed at import if a governing spec file is missing/empty.
        _read_spec_bytes(entry.spec_path)
        registry[entry.surface] = entry
    return registry


_REGISTRY: dict[SettlementSurface, ConstitutionEntry] = _build_registry()

# Computed once at import: a stable policy_hash per surface.
_POLICY_HASHES: dict[SettlementSurface, str] = {
    surface: constitution_policy_hash(entry) for surface, entry in _REGISTRY.items()
}


def get_entry(surface: SettlementSurface) -> ConstitutionEntry:
    """Return the registry entry for a surface, or raise ConstitutionError."""
    if not isinstance(surface, SettlementSurface):
        raise TypeError("surface must be a SettlementSurface")
    entry = _REGISTRY.get(surface)
    if entry is None:
        raise ConstitutionError(f"no constitution entry for surface: {surface}")
    return entry


def policy_hash_for(surface: SettlementSurface) -> str:
    """Return the precomputed canonical policy_hash for a surface."""
    if not isinstance(surface, SettlementSurface):
        raise TypeError("surface must be a SettlementSurface")
    digest = _POLICY_HASHES.get(surface)
    if digest is None:
        raise ConstitutionError(f"no policy_hash for surface: {surface}")
    return digest


def all_surfaces() -> tuple[SettlementSurface, ...]:
    """Return all registered surfaces in registry-insertion order."""
    return tuple(_REGISTRY.keys())


# ---------------------------------------------------------------------------
# Receipt binding: ConstitutionReceiptBody (mirrors derivative_settlement_receipts)
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class ConstitutionReceiptBody:
    """Hash-stable constitution receipt body.

    Binds a settlement to the rule that authorized it: ``policy_id`` +
    ``policy_hash`` + ``gate_output`` + ``claimed_verdict``, plus the pre/post
    state roots and the witness hash. The body documents in ``decided_scope``
    that the bound rule decides admission, not pricing.

    ENFORCEMENT STATUS (v1):
      * ``policy_hash``, ``gate_output``, ``claimed_verdict`` and ``witness_hash``
        are ENFORCED by ``verify_constitution`` in the re-runner: the supplied
        witness must hash to ``witness_hash`` (so a verdict cannot be satisfied
        by substituting a different swap), and the re-derived verdict must equal
        ``claimed_verdict``.
      * ``pre_state_root`` / ``post_state_root`` are carried for receipt
        completeness and shape-validated, but state-root <-> witness binding is
        Phase-2 E2E wiring and is NOT enforced against live state in v1.

    reject-is-no-op: a rejected receipt must carry
    ``post_state_root == pre_state_root``.
    """

    surface_id: str
    policy_id: str
    policy_hash: str
    gate_output: str
    claimed_verdict: int  # 0 | 1
    pre_state_root: str
    post_state_root: str
    witness_hash: str
    accepted: bool
    decided_scope: str = TAU_CONSTITUTION_DECIDED_SCOPE
    rejection_code: str = ""

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema": TAU_CONSTITUTION_RECEIPT_SCHEMA,
            "surface_id": self.surface_id,
            "policy_id": self.policy_id,
            "policy_hash": self.policy_hash,
            "gate_output": self.gate_output,
            "claimed_verdict": int(self.claimed_verdict),
            "pre_state_root": self.pre_state_root,
            "post_state_root": self.post_state_root,
            "witness_hash": self.witness_hash,
            "accepted": bool(self.accepted),
            "decided_scope": self.decided_scope,
            "rejection_code": self.rejection_code,
        }


def _is_hash_ref(value: object) -> bool:
    return isinstance(value, str) and _HEX_32_RE.fullmatch(value) is not None


def _valid_token(value: object) -> bool:
    return isinstance(value, str) and _TOKEN_RE.fullmatch(value) is not None


def constitution_receipt_hash(body: Mapping[str, Any]) -> str:
    """Domain-separated hash of a constitution receipt body."""
    return sha256_hex(
        domain_sep_bytes(TAU_CONSTITUTION_RECEIPT_HASH_DOMAIN)
        + canonical_json_bytes(dict(body))
    )


def validate_constitution_receipt_body(body: object) -> tuple[bool, str]:
    """Validate the deterministic constitution receipt body contract.

    Returns ``(ok, stable_code)``. reject-is-no-op is enforced: a rejected
    (``accepted == False``) body must carry ``post_state_root == pre_state_root``.
    """
    if not isinstance(body, Mapping):
        return False, "body_type"
    if body.get("schema") != TAU_CONSTITUTION_RECEIPT_SCHEMA:
        return False, "schema"
    if not _valid_token(body.get("surface_id")):
        return False, "surface_id"
    if not _valid_token(body.get("policy_id")):
        return False, "policy_id"
    if not _is_hash_ref(body.get("policy_hash")):
        return False, "policy_hash"
    gate_output = body.get("gate_output")
    if not isinstance(gate_output, str) or re.fullmatch(r"o\d+", gate_output) is None:
        return False, "gate_output"
    verdict = body.get("claimed_verdict")
    if not isinstance(verdict, int) or isinstance(verdict, bool) or verdict not in (0, 1):
        return False, "claimed_verdict"
    for key in ("pre_state_root", "post_state_root", "witness_hash"):
        if not _is_hash_ref(body.get(key)):
            return False, key
    # decided_scope must be the pinned constant, not merely a well-formed token.
    # A receipt cannot claim a richer scope (e.g. "pricing_correctness") than the
    # rule actually decides — that would be an overclaim path.
    if body.get("decided_scope") != TAU_CONSTITUTION_DECIDED_SCOPE:
        return False, "decided_scope"
    accepted = body.get("accepted")
    if not isinstance(accepted, bool):
        return False, "accepted"
    # accepted MUST equal (claimed_verdict == 1). Otherwise a receipt could mark
    # a settlement accepted while claiming verdict 0 (or reject while claiming 1),
    # decoupling the human-visible flag from the rule's verdict.
    if accepted != (verdict == 1):
        return False, "accepted_verdict_mismatch"
    rejection_code = body.get("rejection_code")
    if not isinstance(rejection_code, str):
        return False, "rejection_code"
    if accepted and rejection_code:
        return False, "accepted_rejection_code"
    if not accepted:
        if not rejection_code or not _valid_token(rejection_code):
            return False, "missing_rejection_code"
        if body.get("post_state_root") != body.get("pre_state_root"):
            return False, "rejected_state_changed"
    return True, "ok"


def make_constitution_receipt(body: ConstitutionReceiptBody) -> dict[str, Any]:
    """Build a hash-bound constitution receipt envelope."""
    body_dict = body.to_dict()
    ok, reason = validate_constitution_receipt_body(body_dict)
    if not ok:
        raise ValueError(f"invalid constitution receipt body: {reason}")
    return {
        "schema": TAU_CONSTITUTION_RECEIPT_SCHEMA,
        "body": body_dict,
        "receipt_hash": constitution_receipt_hash(body_dict),
    }


def verify_constitution_receipt(receipt: object) -> tuple[bool, str]:
    """Verify a hash-bound constitution receipt envelope (structure only).

    This checks body well-formedness and hash binding. It does NOT re-run the
    governing rule — that is :func:`verify_constitution` in the re-runner module.
    """
    if not isinstance(receipt, Mapping):
        return False, "receipt_type"
    if receipt.get("schema") != TAU_CONSTITUTION_RECEIPT_SCHEMA:
        return False, "schema"
    body = receipt.get("body")
    if not isinstance(body, Mapping):
        return False, "body"
    ok, reason = validate_constitution_receipt_body(body)
    if not ok:
        return False, reason
    if receipt.get("receipt_hash") != constitution_receipt_hash(body):
        return False, "receipt_hash"
    return True, "ok"


def bind_constitution_into_receipt(
    tx_receipt_body: Mapping[str, Any],
    entry: ConstitutionEntry,
    verdict: int,
) -> dict[str, Any]:
    """Additively bind a (policy_id, policy_hash, ...) tuple into a spot tx receipt.

    Mirrors the existing ``batch_cutoff`` ``(policy_id, policy_digest)`` precedent
    in ``zeno_ledger_v0``: it returns a NEW dict (pure; the input is not mutated)
    with a ``constitution`` sub-object carrying the binding. This does not alter
    the consensus tx receipt schema; it is additive client-side evidence.
    """
    if not isinstance(tx_receipt_body, Mapping):
        raise TypeError("tx_receipt_body must be a Mapping")
    if not isinstance(entry, ConstitutionEntry):
        raise TypeError("entry must be a ConstitutionEntry")
    if not isinstance(verdict, int) or isinstance(verdict, bool) or verdict not in (0, 1):
        raise ValueError("verdict must be 0 or 1")
    out = dict(tx_receipt_body)
    out["constitution"] = {
        "schema": TAU_CONSTITUTION_SCHEMA_V1,
        "surface_id": entry.surface_id,
        "policy_id": entry.spec_id,
        "policy_hash": constitution_policy_hash(entry),
        "gate_output": entry.gate_output,
        "witness_encoding_version": entry.witness_encoding_version,
        "claimed_verdict": int(verdict),
        "decided_scope": TAU_CONSTITUTION_DECIDED_SCOPE,
    }
    return out
