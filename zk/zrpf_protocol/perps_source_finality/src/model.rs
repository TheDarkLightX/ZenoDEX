use alloc::collections::{BTreeMap, BTreeSet};
use alloc::vec::Vec;
use core::fmt;
use core::marker::PhantomData;

use serde::de::{self, SeqAccess, Visitor};
use serde::{Deserialize, Deserializer, Serialize};
use zenodex_zrpf_protocol_v3::{
    ApplicationIdV3, CommitmentV3, DomainIdV3, ValueTransferKindV2, ValueTransferSetV2,
    ValueTransferV2, MAX_VALUE_TRANSFERS_PER_SET_V2,
};

use crate::PerpsSourceFinalityReferenceErrorV1;

pub const PROPOSED_PERPS_COLLATERAL_ROWS_VERSION_V1: u16 = 1;
pub const MAX_PERPS_COLLATERAL_ROWS_V1: usize = MAX_VALUE_TRANSFERS_PER_SET_V2 * 2;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PerpsCollateralReferenceContextV1 {
    application_id: ApplicationIdV3,
    chain_or_domain_id: DomainIdV3,
    epoch_id: u64,
    perps_lane_id: CommitmentV3,
    counterparty_lane_id: CommitmentV3,
    deadline_epoch: u64,
}

impl PerpsCollateralReferenceContextV1 {
    pub fn new(
        application_id: ApplicationIdV3,
        chain_or_domain_id: DomainIdV3,
        epoch_id: u64,
        perps_lane_id: CommitmentV3,
        counterparty_lane_id: CommitmentV3,
        deadline_epoch: u64,
    ) -> Result<Self, PerpsSourceFinalityReferenceErrorV1> {
        if perps_lane_id == counterparty_lane_id {
            return Err(PerpsSourceFinalityReferenceErrorV1::InvalidContext(
                "counterparty_lane_id",
            ));
        }
        if deadline_epoch < epoch_id {
            return Err(PerpsSourceFinalityReferenceErrorV1::InvalidContext(
                "deadline_epoch",
            ));
        }
        Ok(Self {
            application_id,
            chain_or_domain_id,
            epoch_id,
            perps_lane_id,
            counterparty_lane_id,
            deadline_epoch,
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

    pub const fn perps_lane_id(self) -> CommitmentV3 {
        self.perps_lane_id
    }

    pub const fn counterparty_lane_id(self) -> CommitmentV3 {
        self.counterparty_lane_id
    }

    pub const fn deadline_epoch(self) -> u64 {
        self.deadline_epoch
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
/// Host-proposed source bindings carried by `ValueTransferV2`.
///
/// Construction establishes nonzero typed commitments only. A governed source
/// verifier must authenticate the transition, receipt claim, and actor scope
/// before they carry authority. Deposit and withdrawal derivation additionally
/// requires the actor scope to match the pubkey committed by the perps action.
pub struct ProposedSourceEvidenceV1 {
    source_state_transition_hash: CommitmentV3,
    source_receipt_claim_hash: CommitmentV3,
    counterparty_actor_scope_hash: CommitmentV3,
}

impl ProposedSourceEvidenceV1 {
    pub const fn new(
        source_state_transition_hash: CommitmentV3,
        source_receipt_claim_hash: CommitmentV3,
        counterparty_actor_scope_hash: CommitmentV3,
    ) -> Self {
        Self {
            source_state_transition_hash,
            source_receipt_claim_hash,
            counterparty_actor_scope_hash,
        }
    }

    pub const fn source_state_transition_hash(self) -> CommitmentV3 {
        self.source_state_transition_hash
    }

    pub const fn source_receipt_claim_hash(self) -> CommitmentV3 {
        self.source_receipt_claim_hash
    }

    pub const fn counterparty_actor_scope_hash(self) -> CommitmentV3 {
        self.counterparty_actor_scope_hash
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PerpsCollateralTransferRowV1 {
    row_version: u16,
    transfer_id: [u8; 32],
    action_index: u32,
    kind: ValueTransferKindV2,
    lane_id: CommitmentV3,
    counterparty_lane_id: CommitmentV3,
    asset_id: CommitmentV3,
    debit_atoms: u128,
    credit_atoms: u128,
    source_state_transition_hash: CommitmentV3,
    source_receipt_claim_hash: CommitmentV3,
}

impl PerpsCollateralTransferRowV1 {
    pub const fn action_index(&self) -> u32 {
        self.action_index
    }

    pub const fn lane_id(&self) -> CommitmentV3 {
        self.lane_id
    }

    pub const fn debit_atoms(&self) -> u128 {
        self.debit_atoms
    }

    pub const fn credit_atoms(&self) -> u128 {
        self.credit_atoms
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ProposedPerpsCollateralRowsV1 {
    proposal_version: u16,
    perps_lane_id: CommitmentV3,
    counterparty_lane_id: CommitmentV3,
    deadline_epoch: u64,
    transfer_set: ValueTransferSetV2,
    rows: Vec<PerpsCollateralTransferRowV1>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ProposedPerpsCollateralRowsWireV1 {
    proposal_version: u16,
    perps_lane_id: CommitmentV3,
    counterparty_lane_id: CommitmentV3,
    deadline_epoch: u64,
    transfer_set: ValueTransferSetV2,
    #[serde(deserialize_with = "deserialize_rows")]
    rows: Vec<PerpsCollateralTransferRowV1>,
}

impl ProposedPerpsCollateralRowsV1 {
    pub fn new(
        context: PerpsCollateralReferenceContextV1,
        transfer_set: ValueTransferSetV2,
    ) -> Result<Self, PerpsSourceFinalityReferenceErrorV1> {
        require_transfer_scope(context, &transfer_set)?;
        let rows = expected_rows(&transfer_set)?;
        Self::from_wire(ProposedPerpsCollateralRowsWireV1 {
            proposal_version: PROPOSED_PERPS_COLLATERAL_ROWS_VERSION_V1,
            perps_lane_id: context.perps_lane_id(),
            counterparty_lane_id: context.counterparty_lane_id(),
            deadline_epoch: context.deadline_epoch(),
            transfer_set,
            rows,
        })
    }

    fn from_wire(
        wire: ProposedPerpsCollateralRowsWireV1,
    ) -> Result<Self, PerpsSourceFinalityReferenceErrorV1> {
        let proposal = Self {
            proposal_version: wire.proposal_version,
            perps_lane_id: wire.perps_lane_id,
            counterparty_lane_id: wire.counterparty_lane_id,
            deadline_epoch: wire.deadline_epoch,
            transfer_set: wire.transfer_set,
            rows: wire.rows,
        };
        proposal.validate_self_consistency()?;
        Ok(proposal)
    }

    pub fn validate_self_consistency(&self) -> Result<(), PerpsSourceFinalityReferenceErrorV1> {
        let context = PerpsCollateralReferenceContextV1::new(
            self.transfer_set.application_id(),
            self.transfer_set.chain_or_domain_id(),
            self.transfer_set.epoch_id(),
            self.perps_lane_id,
            self.counterparty_lane_id,
            self.deadline_epoch,
        )?;
        if self.proposal_version != PROPOSED_PERPS_COLLATERAL_ROWS_VERSION_V1 {
            return Err(PerpsSourceFinalityReferenceErrorV1::InvalidContext(
                "proposal_version",
            ));
        }
        require_transfer_scope(context, &self.transfer_set)?;
        require_routes(context, &self.transfer_set)?;
        if self.rows != expected_rows(&self.transfer_set)? {
            return Err(PerpsSourceFinalityReferenceErrorV1::RowSetMismatch);
        }
        require_conservation(&self.rows)
    }

    pub fn rows(&self) -> &[PerpsCollateralTransferRowV1] {
        &self.rows
    }

    pub const fn transfer_set(&self) -> &ValueTransferSetV2 {
        &self.transfer_set
    }
}

impl<'de> Deserialize<'de> for ProposedPerpsCollateralRowsV1 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let wire = ProposedPerpsCollateralRowsWireV1::deserialize(deserializer)?;
        Self::from_wire(wire).map_err(de::Error::custom)
    }
}

fn require_transfer_scope(
    context: PerpsCollateralReferenceContextV1,
    transfer_set: &ValueTransferSetV2,
) -> Result<(), PerpsSourceFinalityReferenceErrorV1> {
    transfer_set.validate_self_consistency()?;
    if transfer_set.application_id() != context.application_id()
        || transfer_set.chain_or_domain_id() != context.chain_or_domain_id()
        || transfer_set.epoch_id() != context.epoch_id()
    {
        return Err(PerpsSourceFinalityReferenceErrorV1::InvalidContext(
            "transfer_scope",
        ));
    }
    Ok(())
}

fn require_routes(
    context: PerpsCollateralReferenceContextV1,
    transfer_set: &ValueTransferSetV2,
) -> Result<(), PerpsSourceFinalityReferenceErrorV1> {
    for transfer in transfer_set.transfers() {
        let (source, destination) = expected_route(context, transfer.kind());
        if transfer.source_lane_id() != source || transfer.destination_lane_id() != destination {
            return Err(PerpsSourceFinalityReferenceErrorV1::WrongCounterparty {
                action_index: transfer.action_index(),
            });
        }
        if transfer.deadline_epoch() != context.deadline_epoch() {
            return Err(PerpsSourceFinalityReferenceErrorV1::TransferMismatch {
                action_index: transfer.action_index(),
                field: "deadline_epoch",
            });
        }
    }
    Ok(())
}

pub(crate) fn expected_route(
    context: PerpsCollateralReferenceContextV1,
    kind: ValueTransferKindV2,
) -> (CommitmentV3, CommitmentV3) {
    match kind {
        ValueTransferKindV2::InsuranceSeed | ValueTransferKindV2::CollateralDeposit => {
            (context.counterparty_lane_id(), context.perps_lane_id())
        }
        ValueTransferKindV2::CollateralWithdrawal => {
            (context.perps_lane_id(), context.counterparty_lane_id())
        }
    }
}

fn expected_rows(
    transfer_set: &ValueTransferSetV2,
) -> Result<Vec<PerpsCollateralTransferRowV1>, PerpsSourceFinalityReferenceErrorV1> {
    let capacity = transfer_set
        .transfers()
        .len()
        .checked_mul(2)
        .ok_or(PerpsSourceFinalityReferenceErrorV1::ConservationOverflow)?;
    let mut rows = Vec::with_capacity(capacity);
    for transfer in transfer_set.transfers() {
        let transfer_id = transfer.canonical_id()?.into_bytes();
        rows.push(row_from_transfer(transfer, transfer_id, true));
        rows.push(row_from_transfer(transfer, transfer_id, false));
    }
    rows.sort_by_key(|row| (row.transfer_id, row.lane_id));
    let mut keys = BTreeSet::new();
    for row in &rows {
        if !keys.insert((row.transfer_id, row.lane_id)) {
            return Err(PerpsSourceFinalityReferenceErrorV1::RowSetMismatch);
        }
    }
    Ok(rows)
}

fn row_from_transfer(
    transfer: &ValueTransferV2,
    transfer_id: [u8; 32],
    source: bool,
) -> PerpsCollateralTransferRowV1 {
    PerpsCollateralTransferRowV1 {
        row_version: PROPOSED_PERPS_COLLATERAL_ROWS_VERSION_V1,
        transfer_id,
        action_index: transfer.action_index(),
        kind: transfer.kind(),
        lane_id: if source {
            transfer.source_lane_id()
        } else {
            transfer.destination_lane_id()
        },
        counterparty_lane_id: if source {
            transfer.destination_lane_id()
        } else {
            transfer.source_lane_id()
        },
        asset_id: transfer.asset_id(),
        debit_atoms: if source { transfer.amount_atoms() } else { 0 },
        credit_atoms: if source { 0 } else { transfer.amount_atoms() },
        source_state_transition_hash: transfer.source_state_transition_hash(),
        source_receipt_claim_hash: transfer.source_receipt_claim_hash(),
    }
}

fn require_conservation(
    rows: &[PerpsCollateralTransferRowV1],
) -> Result<(), PerpsSourceFinalityReferenceErrorV1> {
    let mut totals = BTreeMap::<CommitmentV3, (u128, u128)>::new();
    for row in rows {
        let entry = totals.entry(row.asset_id).or_insert((0, 0));
        entry.0 = entry
            .0
            .checked_add(row.debit_atoms)
            .ok_or(PerpsSourceFinalityReferenceErrorV1::ConservationOverflow)?;
        entry.1 = entry
            .1
            .checked_add(row.credit_atoms)
            .ok_or(PerpsSourceFinalityReferenceErrorV1::ConservationOverflow)?;
    }
    if totals.values().any(|(debit, credit)| debit != credit) {
        return Err(PerpsSourceFinalityReferenceErrorV1::ConservationMismatch);
    }
    Ok(())
}

fn deserialize_rows<'de, D>(deserializer: D) -> Result<Vec<PerpsCollateralTransferRowV1>, D::Error>
where
    D: Deserializer<'de>,
{
    deserializer.deserialize_seq(RowVisitor {
        marker: PhantomData,
    })
}

struct RowVisitor<T> {
    marker: PhantomData<T>,
}

impl<'de, T> Visitor<'de> for RowVisitor<T>
where
    T: Deserialize<'de>,
{
    type Value = Vec<T>;

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "at most {MAX_PERPS_COLLATERAL_ROWS_V1} rows")
    }

    fn visit_seq<A>(self, mut sequence: A) -> Result<Self::Value, A::Error>
    where
        A: SeqAccess<'de>,
    {
        let declared = sequence.size_hint().unwrap_or(0);
        if declared > MAX_PERPS_COLLATERAL_ROWS_V1 {
            return Err(de::Error::custom(
                PerpsSourceFinalityReferenceErrorV1::TooManyRows {
                    actual: declared,
                    maximum: MAX_PERPS_COLLATERAL_ROWS_V1,
                },
            ));
        }
        let mut rows = Vec::with_capacity(declared.min(MAX_PERPS_COLLATERAL_ROWS_V1));
        while let Some(row) = sequence.next_element()? {
            if rows.len() == MAX_PERPS_COLLATERAL_ROWS_V1 {
                return Err(de::Error::custom(
                    PerpsSourceFinalityReferenceErrorV1::TooManyRows {
                        actual: MAX_PERPS_COLLATERAL_ROWS_V1 + 1,
                        maximum: MAX_PERPS_COLLATERAL_ROWS_V1,
                    },
                ));
            }
            rows.push(row);
        }
        Ok(rows)
    }
}
