use serde::{de, Deserialize, Deserializer, Serialize};
use zenodex_zrpf_protocol_v3::{ApplicationIdV3, CommitmentV3, DomainIdV3};

use crate::ZusdValueFlowErrorV1;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ZusdValueFlowContextInputV1 {
    pub application_id: ApplicationIdV3,
    pub chain_or_domain_id: DomainIdV3,
    pub epoch_id: u64,
    pub zusd_asset_id: CommitmentV3,
    pub collateral_asset_id: CommitmentV3,
    pub stability_pool_scope_id: CommitmentV3,
    pub protocol_scope_id: CommitmentV3,
    pub mint_authority_scope_id: CommitmentV3,
    pub burn_authority_scope_id: CommitmentV3,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub struct ZusdValueFlowContextV1 {
    application_id: ApplicationIdV3,
    chain_or_domain_id: DomainIdV3,
    epoch_id: u64,
    zusd_asset_id: CommitmentV3,
    collateral_asset_id: CommitmentV3,
    stability_pool_scope_id: CommitmentV3,
    protocol_scope_id: CommitmentV3,
    mint_authority_scope_id: CommitmentV3,
    burn_authority_scope_id: CommitmentV3,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ZusdValueFlowContextWireV1 {
    application_id: ApplicationIdV3,
    chain_or_domain_id: DomainIdV3,
    epoch_id: u64,
    zusd_asset_id: CommitmentV3,
    collateral_asset_id: CommitmentV3,
    stability_pool_scope_id: CommitmentV3,
    protocol_scope_id: CommitmentV3,
    mint_authority_scope_id: CommitmentV3,
    burn_authority_scope_id: CommitmentV3,
}

impl ZusdValueFlowContextV1 {
    pub fn new(input: ZusdValueFlowContextInputV1) -> Result<Self, ZusdValueFlowErrorV1> {
        if input.zusd_asset_id == input.collateral_asset_id {
            return Err(ZusdValueFlowErrorV1::InvalidContext("asset_id_alias"));
        }
        if input.stability_pool_scope_id == input.protocol_scope_id {
            return Err(ZusdValueFlowErrorV1::InvalidContext("reserved_scope_alias"));
        }
        Ok(Self {
            application_id: input.application_id,
            chain_or_domain_id: input.chain_or_domain_id,
            epoch_id: input.epoch_id,
            zusd_asset_id: input.zusd_asset_id,
            collateral_asset_id: input.collateral_asset_id,
            stability_pool_scope_id: input.stability_pool_scope_id,
            protocol_scope_id: input.protocol_scope_id,
            mint_authority_scope_id: input.mint_authority_scope_id,
            burn_authority_scope_id: input.burn_authority_scope_id,
        })
    }

    pub const fn application_id(self) -> ApplicationIdV3 {
        self.application_id
    }

    pub const fn chain_or_domain_id(self) -> DomainIdV3 {
        self.chain_or_domain_id
    }

    pub const fn epoch_id(self) -> u64 {
        self.epoch_id
    }

    pub const fn zusd_asset_id(self) -> CommitmentV3 {
        self.zusd_asset_id
    }

    pub const fn collateral_asset_id(self) -> CommitmentV3 {
        self.collateral_asset_id
    }

    pub const fn stability_pool_scope_id(self) -> CommitmentV3 {
        self.stability_pool_scope_id
    }

    pub const fn protocol_scope_id(self) -> CommitmentV3 {
        self.protocol_scope_id
    }

    pub const fn mint_authority_scope_id(self) -> CommitmentV3 {
        self.mint_authority_scope_id
    }

    pub const fn burn_authority_scope_id(self) -> CommitmentV3 {
        self.burn_authority_scope_id
    }
}

impl<'de> Deserialize<'de> for ZusdValueFlowContextV1 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let wire = ZusdValueFlowContextWireV1::deserialize(deserializer)?;
        Self::new(ZusdValueFlowContextInputV1 {
            application_id: wire.application_id,
            chain_or_domain_id: wire.chain_or_domain_id,
            epoch_id: wire.epoch_id,
            zusd_asset_id: wire.zusd_asset_id,
            collateral_asset_id: wire.collateral_asset_id,
            stability_pool_scope_id: wire.stability_pool_scope_id,
            protocol_scope_id: wire.protocol_scope_id,
            mint_authority_scope_id: wire.mint_authority_scope_id,
            burn_authority_scope_id: wire.burn_authority_scope_id,
        })
        .map_err(de::Error::custom)
    }
}

/// Host-proposed source bindings. These commitments carry no proof authority.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ProposedZusdSourceEvidenceV1 {
    source_state_transition_hash: CommitmentV3,
    source_receipt_claim_hash: CommitmentV3,
}

impl ProposedZusdSourceEvidenceV1 {
    pub const fn new(
        source_state_transition_hash: CommitmentV3,
        source_receipt_claim_hash: CommitmentV3,
    ) -> Self {
        Self {
            source_state_transition_hash,
            source_receipt_claim_hash,
        }
    }

    pub const fn source_state_transition_hash(self) -> CommitmentV3 {
        self.source_state_transition_hash
    }

    pub const fn source_receipt_claim_hash(self) -> CommitmentV3 {
        self.source_receipt_claim_hash
    }
}
