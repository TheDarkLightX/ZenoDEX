"""Private governed Spot V7 V3 policy capability and policy value objects.

The V3 policy extends the existing authority-false V2 operational material with
an exact ZenoLedger chain identifier, one complete sampled-retrievability
policy, and one acyclic lagged-checkpoint beacon policy.  Construction of the
governed capability remains owned by the signed-manifest provenance adapter.
No value in this module grants release, settlement, or production authority.
"""

from __future__ import annotations

import hashlib
import re
from dataclasses import dataclass
from typing import NoReturn, SupportsIndex, final

from src.integration._zrpf_spot_v7_operational_capability_v2 import (
    _GovernedOperationalPolicyMaterialV2,
)
from src.integration._zrpf_spot_v7_operational_gate import (
    _GovernedOperationalPolicyProjectionV1,
)
from src.integration._zrpf_spot_v7_operational_mechanics import (
    _TestOnlySpotV7OperationalPolicyV1,
)
from src.integration._zrpf_spot_v7_zeno_ledger_finality_contract import (
    derive_zeno_ledger_finality_network_id_v1,
    derive_zeno_ledger_finality_protocol_id_v2,
    derive_zeno_ledger_finality_protocol_id_v3,
)
from src.integration.zeno_ledger_v0 import hash_v0
from src.integration.zrpf_sampled_retrievability_v1.model import (
    SampledRetrievabilityPolicyV1,
    require_root,
    require_u64,
)

MAX_OPERATIONAL_POLICY_PROVENANCE_BYTES_V2 = 4 * 1_024 * 1_024
MAX_BEACON_SOURCE_EPOCH_LAG_V1 = 64
_MAX_U64 = (1 << 64) - 1
_CHAIN_ID_RE = re.compile(r"^[A-Za-z0-9._:-]{1,128}$")


def _require_chain_id(value: object) -> str:
    if type(value) is not str or _CHAIN_ID_RE.fullmatch(value) is None:
        raise ValueError("zeno_ledger_chain_id must be a bounded canonical token")
    return value


def derive_zeno_ledger_checkpoint_beacon_source_id_v1(chain_id: str) -> str:
    """Derive one source identity from the exact governed ZenoLedger chain."""

    canonical_chain = _require_chain_id(chain_id)
    return hash_v0(
        "zrpf_spot_v7_zeno_ledger_checkpoint_beacon_source_v1",
        {
            "chain_id": canonical_chain,
            "network_id": derive_zeno_ledger_finality_network_id_v1(canonical_chain),
            "protocol_id": derive_zeno_ledger_finality_protocol_id_v2(),
        },
    )


@dataclass(frozen=True, slots=True)
class BeaconPolicyV1:
    """Acyclic policy for deriving a beacon from a prior finalized checkpoint."""

    policy_revision: int
    activation_epoch: int
    revocation_epoch: int | None
    source_id: str
    source_network_id: str
    source_protocol_id: str
    source_epoch_lag: int

    def __post_init__(self) -> None:
        require_u64(self.policy_revision, name="beacon policy_revision")
        require_u64(self.activation_epoch, name="beacon activation_epoch")
        if self.revocation_epoch is not None:
            require_u64(self.revocation_epoch, name="beacon revocation_epoch")
            if self.revocation_epoch <= self.activation_epoch:
                raise ValueError("beacon revocation must follow activation")
        require_root(self.source_id, name="beacon source_id")
        require_root(self.source_network_id, name="beacon source_network_id")
        require_root(self.source_protocol_id, name="beacon source_protocol_id")
        if type(self.source_epoch_lag) is not int or not (
            1 <= self.source_epoch_lag <= MAX_BEACON_SOURCE_EPOCH_LAG_V1
        ):
            raise ValueError("beacon source_epoch_lag is outside 1..64")
        if self.activation_epoch < self.source_epoch_lag:
            raise ValueError("beacon activation precedes the first lagged source epoch")

    @property
    def policy_root(self) -> str:
        return hash_v0("zrpf_spot_v7_lagged_checkpoint_beacon_policy_v1", self.to_document())

    def is_active_at(self, epoch: int) -> bool:
        require_u64(epoch, name="beacon policy evaluation epoch")
        return self.activation_epoch <= epoch and (
            self.revocation_epoch is None or epoch < self.revocation_epoch
        )

    def to_document(self) -> dict[str, object]:
        return {
            "activation_epoch": self.activation_epoch,
            "policy_revision": self.policy_revision,
            "revocation_epoch": self.revocation_epoch,
            "source_epoch_lag": self.source_epoch_lag,
            "source_id": self.source_id,
            "source_network_id": self.source_network_id,
            "source_protocol_id": self.source_protocol_id,
        }


@dataclass(frozen=True, slots=True)
class _GovernedOperationalPolicyMaterialV3:
    """Complete signed V3 policy material before the private governed seal."""

    base_material: _GovernedOperationalPolicyMaterialV2
    zeno_ledger_chain_id: str
    sampled_retrievability_policy: SampledRetrievabilityPolicyV1
    beacon_policy: BeaconPolicyV1

    def __post_init__(self) -> None:
        if type(self.base_material) is not _GovernedOperationalPolicyMaterialV2:
            raise TypeError("base_material must be exact V2 operational material")
        if type(self.sampled_retrievability_policy) is not SampledRetrievabilityPolicyV1:
            raise TypeError("sampled policy must be exact SampledRetrievabilityPolicyV1")
        if type(self.beacon_policy) is not BeaconPolicyV1:
            raise TypeError("beacon policy must be exact BeaconPolicyV1")
        chain_id = _require_chain_id(self.zeno_ledger_chain_id)
        base = self.base_material
        sampled = self.sampled_retrievability_policy
        beacon = self.beacon_policy
        expected_network = derive_zeno_ledger_finality_network_id_v1(chain_id)
        expected_settlement_protocol = derive_zeno_ledger_finality_protocol_id_v3()
        expected_beacon_source_protocol = derive_zeno_ledger_finality_protocol_id_v2()
        expected_source = derive_zeno_ledger_checkpoint_beacon_source_id_v1(chain_id)
        checks = (
            (sampled.application_id == base.application_id, "sampled application mismatch"),
            (
                sampled.chain_or_domain_id == base.chain_or_domain_id,
                "sampled domain mismatch",
            ),
            (
                sampled.storage_policy_hash == base.storage_policy_hash,
                "sampled storage policy mismatch",
            ),
            (
                sampled.minimum_retention_epochs == base.minimum_retention_epochs,
                "sampled minimum retention mismatch",
            ),
            (
                sampled.minimum_remaining_epochs == base.minimum_remaining_epochs,
                "sampled remaining retention mismatch",
            ),
            (base.finality_network_id == expected_network, "ZenoLedger network mismatch"),
            (
                base.finality_protocol_id == expected_settlement_protocol,
                "ZenoLedger settlement finality protocol mismatch",
            ),
            (beacon.source_network_id == expected_network, "beacon network mismatch"),
            (
                beacon.source_protocol_id == expected_beacon_source_protocol,
                "beacon source finality protocol mismatch",
            ),
            (beacon.source_id == expected_source, "beacon source mismatch"),
            (sampled.beacon_source_id == beacon.source_id, "sampled beacon source mismatch"),
            (
                sampled.beacon_policy_hash == beacon.policy_root,
                "sampled beacon policy mismatch",
            ),
            (
                sampled.activation_epoch >= beacon.activation_epoch,
                "sampled policy activates before beacon policy",
            ),
            (
                sampled.activation_epoch >= beacon.source_epoch_lag,
                "sampled policy activates before a lagged source can exist",
            ),
        )
        for accepted, detail in checks:
            if not accepted:
                raise ValueError(detail)

    def _to_authority_false_store_policy(self) -> _TestOnlySpotV7OperationalPolicyV1:
        return self.base_material._to_authority_false_store_policy()


@dataclass(frozen=True, slots=True)
class _GovernedOperationalPolicyProvenanceV2:
    """Exact signed-manifest evidence retained with a governed V3 policy."""

    evidence_root: str
    exact_evidence_bytes: bytes
    manifest_sha256: str
    signer_registry_hash: str
    signature_quorum_report_hash: str
    policy_revision: int
    policy_activation_epoch: int
    policy_revocation_epoch: int | None
    signer_registry_revision: int
    signer_registry_activation_epoch: int
    signer_registry_revocation_epoch: int | None
    evaluation_epoch: int

    def __post_init__(self) -> None:
        for name in (
            "evidence_root",
            "signer_registry_hash",
            "signature_quorum_report_hash",
        ):
            require_root(getattr(self, name), name=f"policy provenance {name}")
        if (
            type(self.exact_evidence_bytes) is not bytes
            or not self.exact_evidence_bytes
            or len(self.exact_evidence_bytes) > MAX_OPERATIONAL_POLICY_PROVENANCE_BYTES_V2
        ):
            raise ValueError("policy provenance bytes are empty or oversized")
        expected_root = "0x" + hashlib.sha256(self.exact_evidence_bytes).hexdigest()
        if self.evidence_root != expected_root:
            raise ValueError("policy provenance evidence root mismatch")
        if (
            type(self.manifest_sha256) is not str
            or len(self.manifest_sha256) != 64
            or any(character not in "0123456789abcdef" for character in self.manifest_sha256)
        ):
            raise ValueError("policy manifest SHA-256 is not canonical")
        for name in (
            "policy_revision",
            "policy_activation_epoch",
            "signer_registry_revision",
            "signer_registry_activation_epoch",
            "evaluation_epoch",
        ):
            require_u64(getattr(self, name), name=f"policy provenance {name}")
        for name in ("policy_revocation_epoch", "signer_registry_revocation_epoch"):
            value = getattr(self, name)
            if value is not None:
                require_u64(value, name=f"policy provenance {name}")
        self._require_active_at_epoch(self.evaluation_epoch)

    def _require_active_at_epoch(self, epoch: int) -> None:
        require_u64(epoch, name="policy checked epoch")
        for name, activation, revocation in (
            ("operational policy", self.policy_activation_epoch, self.policy_revocation_epoch),
            (
                "operational policy signer registry",
                self.signer_registry_activation_epoch,
                self.signer_registry_revocation_epoch,
            ),
        ):
            if epoch < activation:
                raise ValueError(f"{name} is not active at the checked epoch")
            if revocation is not None and epoch >= revocation:
                raise ValueError(f"{name} is revoked at the checked epoch")


@dataclass(frozen=True, slots=True)
class _GovernedSpotV7OperationalPolicyProjectionV3:
    application_id: str
    chain_or_domain_id: str
    zeno_ledger_chain_id: str
    full_blob_da_policy_root: str
    checkpoint_finality_policy_root: str
    sampled_policy_root: str
    beacon_policy_root: str
    policy_provenance_root: str

    def __post_init__(self) -> None:
        for name in (
            "application_id",
            "chain_or_domain_id",
            "full_blob_da_policy_root",
            "checkpoint_finality_policy_root",
            "sampled_policy_root",
            "beacon_policy_root",
            "policy_provenance_root",
        ):
            require_root(getattr(self, name), name=f"V3 policy projection {name}")
        _require_chain_id(self.zeno_ledger_chain_id)


class _GovernedOperationalPolicySealV3:
    __slots__ = ()


_GOVERNED_OPERATIONAL_POLICY_SEAL_V3 = _GovernedOperationalPolicySealV3()


class _NonTransferableOperationalCapabilityV3:
    __slots__ = ()

    def __setattr__(self, _name: str, _value: object) -> NoReturn:
        raise TypeError("Spot V7 V3 operational capability cannot be mutated")

    def __copy__(self) -> NoReturn:
        raise TypeError("Spot V7 V3 operational capability cannot be copied")

    def __deepcopy__(self, _memo: object) -> NoReturn:
        raise TypeError("Spot V7 V3 operational capability cannot be deep-copied")

    def __reduce__(self) -> NoReturn:
        raise TypeError("Spot V7 V3 operational capability cannot be serialized")

    def __reduce_ex__(self, _protocol: SupportsIndex) -> NoReturn:
        raise TypeError("Spot V7 V3 operational capability cannot be serialized")


@final
class _GovernedSpotV7OperationalPolicyV3(_NonTransferableOperationalCapabilityV3):
    """Signed V3 policy provenance and exact sampled/beacon policy material."""

    __slots__ = ("_material", "_projection", "_provenance", "_seal")

    _material: _GovernedOperationalPolicyMaterialV3
    _projection: _GovernedSpotV7OperationalPolicyProjectionV3
    _provenance: _GovernedOperationalPolicyProvenanceV2
    _seal: _GovernedOperationalPolicySealV3

    def __init__(
        self,
        material: _GovernedOperationalPolicyMaterialV3,
        *,
        provenance: _GovernedOperationalPolicyProvenanceV2,
        seal: _GovernedOperationalPolicySealV3,
    ) -> None:
        if type(material) is not _GovernedOperationalPolicyMaterialV3:
            raise TypeError("governed V3 policy material has the wrong type")
        if type(provenance) is not _GovernedOperationalPolicyProvenanceV2:
            raise TypeError("governed V3 policy provenance has the wrong type")
        if seal is not _GOVERNED_OPERATIONAL_POLICY_SEAL_V3:
            raise TypeError("governed V3 policy requires the module-private seal")
        store_policy = material._to_authority_false_store_policy()
        projection = _GovernedSpotV7OperationalPolicyProjectionV3(
            application_id=material.base_material.application_id,
            chain_or_domain_id=material.base_material.chain_or_domain_id,
            zeno_ledger_chain_id=material.zeno_ledger_chain_id,
            full_blob_da_policy_root=store_policy.full_blob_policy_root,
            checkpoint_finality_policy_root=store_policy.checkpoint_finality_policy_root,
            sampled_policy_root=material.sampled_retrievability_policy.policy_root,
            beacon_policy_root=material.beacon_policy.policy_root,
            policy_provenance_root=provenance.evidence_root,
        )
        object.__setattr__(self, "_material", material)
        object.__setattr__(self, "_projection", projection)
        object.__setattr__(self, "_provenance", provenance)
        object.__setattr__(self, "_seal", seal)

    def _has_private_seal(self) -> bool:
        return getattr(self, "_seal", None) is _GOVERNED_OPERATIONAL_POLICY_SEAL_V3

    def _require_live_integrity(self) -> None:
        if not self._has_private_seal():
            raise TypeError("governed V3 policy lacks its private seal")
        if (
            "0x" + hashlib.sha256(self._provenance.exact_evidence_bytes).hexdigest()
            != self._provenance.evidence_root
        ):
            raise ValueError("governed V3 operational policy provenance drift")
        store_policy = self._material._to_authority_false_store_policy()
        expected = _GovernedSpotV7OperationalPolicyProjectionV3(
            application_id=self._material.base_material.application_id,
            chain_or_domain_id=self._material.base_material.chain_or_domain_id,
            zeno_ledger_chain_id=self._material.zeno_ledger_chain_id,
            full_blob_da_policy_root=store_policy.full_blob_policy_root,
            checkpoint_finality_policy_root=store_policy.checkpoint_finality_policy_root,
            sampled_policy_root=self._material.sampled_retrievability_policy.policy_root,
            beacon_policy_root=self._material.beacon_policy.policy_root,
            policy_provenance_root=self._provenance.evidence_root,
        )
        if expected != self._projection:
            raise ValueError("governed V3 operational policy projection drift")

    def _require_active_at_epoch_for_governed_da_v2(self, epoch: int) -> None:
        self._require_live_integrity()
        self._provenance._require_active_at_epoch(epoch)
        sampled = self._material.sampled_retrievability_policy
        beacon = self._material.beacon_policy
        if not sampled.is_active_at(epoch) or not beacon.is_active_at(epoch):
            raise ValueError("governed sampled or beacon policy is inactive")
        if len(sampled.active_provider_ids_at(epoch)) < sampled.minimum_provider_responses:
            raise ValueError("insufficient governed active providers at checked epoch")

    def _projection_for_governed_da_v2(
        self,
    ) -> _GovernedSpotV7OperationalPolicyProjectionV3:
        self._require_live_integrity()
        return self._projection

    def _sampled_policy_for_governed_da_v2(self) -> SampledRetrievabilityPolicyV1:
        self._require_live_integrity()
        return self._material.sampled_retrievability_policy

    def _beacon_policy_for_governed_da_v2(self) -> BeaconPolicyV1:
        self._require_live_integrity()
        return self._material.beacon_policy

    def _base_store_policy_for_governed_beacon_v1(
        self,
    ) -> _TestOnlySpotV7OperationalPolicyV1:
        self._require_live_integrity()
        return self._material._to_authority_false_store_policy()

    def _require_active_at_epoch_for_finality_v3(self, epoch: int) -> None:
        """Require the signed policy and signer registry at one finality epoch."""

        self._require_live_integrity()
        self._provenance._require_active_at_epoch(epoch)

    def _base_store_policy_for_finality_v3(
        self,
    ) -> _TestOnlySpotV7OperationalPolicyV1:
        self._require_live_integrity()
        return self._material._to_authority_false_store_policy()

    def _legacy_projection_for_finality_v3(
        self,
    ) -> _GovernedOperationalPolicyProjectionV1:
        self._require_live_integrity()
        return _GovernedOperationalPolicyProjectionV1(
            application_id=self._projection.application_id,
            chain_or_domain_id=self._projection.chain_or_domain_id,
            full_blob_da_policy_root=self._projection.full_blob_da_policy_root,
            checkpoint_finality_policy_root=self._projection.checkpoint_finality_policy_root,
        )

    def _provenance_for_governed_da_v2(self) -> _GovernedOperationalPolicyProvenanceV2:
        self._require_live_integrity()
        return self._provenance

    def _legacy_projection_for_full_blob_v2(self) -> _GovernedOperationalPolicyProjectionV1:
        self._require_live_integrity()
        return _GovernedOperationalPolicyProjectionV1(
            application_id=self._projection.application_id,
            chain_or_domain_id=self._projection.chain_or_domain_id,
            full_blob_da_policy_root=self._projection.full_blob_da_policy_root,
            checkpoint_finality_policy_root=self._projection.checkpoint_finality_policy_root,
        )

    @property
    def sampled_policy_governance_provenance_verified(self) -> bool:
        self._require_live_integrity()
        return True

    @property
    def current_operational_policy_release_head_verified(self) -> bool:
        return False

    @property
    def beacon_unpredictability_verified(self) -> bool:
        return False

    @property
    def provider_independence_verified(self) -> bool:
        return False

    @property
    def continuous_availability_verified(self) -> bool:
        return False

    @property
    def public_future_availability_verified(self) -> bool:
        return False

    @property
    def release_authority(self) -> bool:
        return False

    @property
    def settlement_authority(self) -> bool:
        return False

    @property
    def production_authority(self) -> bool:
        return False


def _mint_governed_spot_v7_operational_policy_v3(
    material: _GovernedOperationalPolicyMaterialV3,
    *,
    provenance: _GovernedOperationalPolicyProvenanceV2,
) -> _GovernedSpotV7OperationalPolicyV3:
    """Module-private handoff used only by the signed-manifest adapter."""

    return _GovernedSpotV7OperationalPolicyV3(
        material,
        provenance=provenance,
        seal=_GOVERNED_OPERATIONAL_POLICY_SEAL_V3,
    )


def _require_governed_operational_policy_v3(
    value: object,
) -> _GovernedSpotV7OperationalPolicyV3:
    if type(value) is not _GovernedSpotV7OperationalPolicyV3:
        raise TypeError("governed beacon requires exact Spot V7 operational policy V3")
    if not value._has_private_seal():
        raise TypeError("governed beacon requires sealed Spot V7 operational policy V3")
    value._projection_for_governed_da_v2()
    return value
