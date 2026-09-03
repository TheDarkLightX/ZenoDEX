//! Receipt admission for the ASSET_TRANSFER allocation fragment (C9b-1): the Rust twin of
//! `src/core/asset_transfer_receipt_admission_v1.py` (C9a).
//!
//! `verify_asset_transfer_fragment_receipt_v1` takes the receipt-verified module witness
//! (`VerifiedLaneModuleTransitionV1`, mintable only by
//! `verify_asset_transfer_lane_module_receipt_v1` after a succinct-receipt check against the
//! recomputed module journal under an ACTIVE_NEW release image), binds the caller's accepted
//! value to the witness at the journal root, re-runs the wave-B fragment producer, and mints
//! the sealed `VerifiedLaneAllocationFragmentV1` (private fields: constructible only here;
//! the Python twin defines the class in the certificate module, its only consumer, because
//! Python cannot import in a cycle, while Rust seals per module and the certificate module
//! imports this one). The witness carries the rebuilt journal's header for the certificate
//! check's header binding (C9b-2a).
//! The certificate registry registers ASSET_TRANSFER receipt-backed in both languages
//! (C9b-2b), behind the witness-slot gate: an enabled asset-transfer fragment is accepted
//! only when this witness fills its slot.
//!
//! Check order, shared with the Python authority: (0) the boundary: `accepted` is validated
//! (the Python twin re-runs every construction invariant on an exact-typed snapshot), the
//! committed lane root's roots, the prior fragment, and the entitlement row tokens are
//! validated, and the journal root is recomputed; a boundary failure is an `AbiErrorV1`, the
//! Rust analogue of the `TypeError`/`ValueError` the Python admission raises, so the
//! producer's `ACCEPTED_INVALID` is unreachable through either admission; (1) the witness
//! carries a succinct receipt; (2) the receipt-verified module journal root equals the
//! recomputed `module_journal` root (the one equality that binds the caller's value to the
//! proof); (3) the statement root and the command occurrence agree (defensive
//! double-binding); then the producer re-runs with its full check family and (4) the produced
//! `binding_root` must equal the journal's receipt root. Every reject is a value; every input
//! is borrowed immutably, so a reject cannot mutate.
//!
//! Reachability through minted witnesses: the mint point derives every witness scalar from
//! the recomputed journal and enforces the succinct kind, and the witness fields are private,
//! so `WITNESS_KIND_DRIFT`, `WITNESS_STATEMENT_ROOT_DRIFT`, and `WITNESS_OCCURRENCE_DRIFT`
//! can differ only on a forged witness (unreachable here; reachable in Python through
//! `object.__new__`, where they are tested) and `WITNESS_BINDING_ROOT_DRIFT` only on a
//! drifted producer; `WITNESS_JOURNAL_ROOT_DRIFT` is reachable with a witness minted for
//! another occurrence. Divergence, decided: the Python snapshot refuses non-canonical or
//! zero-amount entitlement rows by raising before the producer runs, while this twin
//! validates row tokens at the boundary and leaves ordering and zero amounts to the
//! producer's `ENTITLEMENT_ROWS_NOT_CANONICAL`; the parity vectors cover well-formed inputs.
//!
//! NONCLAIMS: as in the Python module, claimant identity and the split across claimants are
//! caller-chosen at this layer (the coverage fold is keyed on (asset, control_domain)); the
//! succinct-receipt check is inherited from `lane_module_receipt_verification`; this module
//! adds no cryptographic claim of its own. Research-only evidence; authority NONE.

use crate::asset_transfer_lane_module::AssetTransferLaneModuleAcceptedV1;
use crate::canonical::{AbiResultV1, RootV1};
use crate::global_accounting_allocation_certificate::{
    ClaimantEntitlementRowV1, LaneAllocationFragmentV1,
};
use crate::global_accounting_lane_producers::{
    produce_asset_transfer_fragment_v1, ReceiptBackedProducerRejectedV1,
};
use crate::lane_module_receipt_verification::VerifiedLaneModuleTransitionV1;
use crate::proof::ReceiptKindV1;
use crate::release::LaneIdV1;
use crate::state::LaneStateRootV1;

pub const RECEIPT_ADMISSION_SCHEMA_V1: &str = "zenodex/asset-transfer-receipt-admission/v1";

/// Closed witness-binding rejects, checked before the producer runs. The declaration order
/// is the cross-language family order (`RECEIPT_WITNESS_REJECT_CODES_V1` in Python), pinned
/// mechanically by the Python admission suite.
#[allow(non_camel_case_types)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ReceiptWitnessRejectCodeV1 {
    WITNESS_KIND_DRIFT,
    WITNESS_JOURNAL_ROOT_DRIFT,
    WITNESS_STATEMENT_ROOT_DRIFT,
    WITNESS_OCCURRENCE_DRIFT,
    WITNESS_BINDING_ROOT_DRIFT,
}

impl ReceiptWitnessRejectCodeV1 {
    pub const ALL: [Self; 5] = [
        Self::WITNESS_KIND_DRIFT,
        Self::WITNESS_JOURNAL_ROOT_DRIFT,
        Self::WITNESS_STATEMENT_ROOT_DRIFT,
        Self::WITNESS_OCCURRENCE_DRIFT,
        Self::WITNESS_BINDING_ROOT_DRIFT,
    ];

    pub const fn as_str(self) -> &'static str {
        match self {
            Self::WITNESS_KIND_DRIFT => "WITNESS_KIND_DRIFT",
            Self::WITNESS_JOURNAL_ROOT_DRIFT => "WITNESS_JOURNAL_ROOT_DRIFT",
            Self::WITNESS_STATEMENT_ROOT_DRIFT => "WITNESS_STATEMENT_ROOT_DRIFT",
            Self::WITNESS_OCCURRENCE_DRIFT => "WITNESS_OCCURRENCE_DRIFT",
            Self::WITNESS_BINDING_ROOT_DRIFT => "WITNESS_BINDING_ROOT_DRIFT",
        }
    }
}

/// A witness-binding refusal: nothing is minted, every input left unchanged.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ReceiptWitnessRejectedV1 {
    pub code: ReceiptWitnessRejectCodeV1,
    pub lane_id: LaneIdV1,
    pub committed_lane_root: RootV1,
    pub detail: String,
}

/// The admission's closed reject union: a witness-binding refusal or the producer's own
/// reject, passed through unchanged (the Python twin returns the same two value types).
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum AssetTransferFragmentAdmissionRejectedV1 {
    Witness(ReceiptWitnessRejectedV1),
    Producer(ReceiptBackedProducerRejectedV1),
}

/// Opaque receipt-admitted fragment, produced only by this verifier: the fields are private,
/// so no other module (and no deserialiser) can construct one. An out-of-module struct
/// literal does not compile:
///
/// ```compile_fail
/// use zenodex_global_settlement_abi_v1::{RootV1, VerifiedLaneAllocationFragmentV1, LaneAllocationFragmentV1, LaneIdV1, LaneProducerKindV1};
/// let root = RootV1::parse(format!("0x{:064x}", 1u64), "r", false).unwrap();
/// let fragment = LaneAllocationFragmentV1 {
///     lane_id: LaneIdV1::ASSET_TRANSFER, module_release_id: root.clone(), enabled: true,
///     lane_state_root: root.clone(), producer_kind: LaneProducerKindV1::RECEIPT_BACKED,
///     binding_root: root.clone(), controlled_locations: vec![], claimant_entitlements: vec![],
///     unencumbered_reserves: vec![], pending_external_obligations: vec![], terminal_bindings: vec![],
/// };
/// let _forged = VerifiedLaneAllocationFragmentV1 {
///     fragment, module_journal_root: root.clone(), receipt_root: root.clone(),
///     receipt_digest: root.clone(), expected_image_id: root.clone(), chain_id: String::new(),
///     deployment_root: root.clone(), profile_root: root, writer_epoch: 0,
/// };
/// ```
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VerifiedLaneAllocationFragmentV1 {
    fragment: LaneAllocationFragmentV1,
    module_journal_root: RootV1,
    receipt_root: RootV1,
    receipt_digest: RootV1,
    expected_image_id: RootV1,
    chain_id: String,
    deployment_root: RootV1,
    profile_root: RootV1,
    writer_epoch: u64,
}

impl VerifiedLaneAllocationFragmentV1 {
    pub fn fragment(&self) -> &LaneAllocationFragmentV1 {
        &self.fragment
    }

    pub fn module_journal_root(&self) -> &RootV1 {
        &self.module_journal_root
    }

    /// The journal's receipt root, exported only after check (4) held.
    pub fn receipt_root(&self) -> &RootV1 {
        &self.receipt_root
    }

    pub fn receipt_digest(&self) -> &RootV1 {
        &self.receipt_digest
    }

    pub fn expected_image_id(&self) -> &RootV1 {
        &self.expected_image_id
    }

    /// The rebuilt journal's header, bound by the certificate check to the state it checks.
    pub fn chain_id(&self) -> &str {
        &self.chain_id
    }

    pub fn deployment_root(&self) -> &RootV1 {
        &self.deployment_root
    }

    pub fn profile_root(&self) -> &RootV1 {
        &self.profile_root
    }

    pub fn writer_epoch(&self) -> u64 {
        self.writer_epoch
    }
}

fn reject_witness(
    code: ReceiptWitnessRejectCodeV1,
    lane_root: &LaneStateRootV1,
    detail: &'static str,
) -> AssetTransferFragmentAdmissionRejectedV1 {
    AssetTransferFragmentAdmissionRejectedV1::Witness(ReceiptWitnessRejectedV1 {
        code,
        lane_id: lane_root.lane_id,
        committed_lane_root: lane_root.state_root.clone(),
        detail: detail.to_owned(),
    })
}

/// Check (0): the type boundary. Python rebuilds every caller value through its constructors
/// and raises; here every public validator runs, and a failure is an error, not a reject.
fn validate_admission_boundary_v1(
    accepted: &AssetTransferLaneModuleAcceptedV1,
    lane_root: &LaneStateRootV1,
    prior_fragment: &LaneAllocationFragmentV1,
    claimant_entitlements: &[ClaimantEntitlementRowV1],
) -> AbiResultV1<()> {
    accepted.validate()?;
    lane_root
        .module_release_id
        .validate("committed lane root module release id", false)?;
    lane_root
        .state_root
        .validate("committed lane root state root", true)?;
    prior_fragment.validate()?;
    for row in claimant_entitlements {
        row.validate()?;
    }
    Ok(())
}

/// Admit one fragment only through the receipt-verified module witness (see the module
/// documentation for the check order and the reachability of each code).
pub fn verify_asset_transfer_fragment_receipt_v1(
    witness: &VerifiedLaneModuleTransitionV1,
    accepted: &AssetTransferLaneModuleAcceptedV1,
    lane_root: &LaneStateRootV1,
    prior_fragment: &LaneAllocationFragmentV1,
    claimant_entitlements: &[ClaimantEntitlementRowV1],
) -> AbiResultV1<Result<VerifiedLaneAllocationFragmentV1, AssetTransferFragmentAdmissionRejectedV1>>
{
    validate_admission_boundary_v1(accepted, lane_root, prior_fragment, claimant_entitlements)?;
    let journal = &accepted.module_journal;
    let journal_root = journal.journal_root()?;
    if witness.receipt_kind() != ReceiptKindV1::SUCCINCT {
        return Ok(Err(reject_witness(
            ReceiptWitnessRejectCodeV1::WITNESS_KIND_DRIFT,
            lane_root,
            "witness kind",
        )));
    }
    if witness.module_journal_root() != &journal_root {
        return Ok(Err(reject_witness(
            ReceiptWitnessRejectCodeV1::WITNESS_JOURNAL_ROOT_DRIFT,
            lane_root,
            "journal root",
        )));
    }
    if witness.statement_root() != &accepted.statement_root {
        return Ok(Err(reject_witness(
            ReceiptWitnessRejectCodeV1::WITNESS_STATEMENT_ROOT_DRIFT,
            lane_root,
            "statement root",
        )));
    }
    if witness.command_occurrence_id() != &journal.command_occurrence_id {
        return Ok(Err(reject_witness(
            ReceiptWitnessRejectCodeV1::WITNESS_OCCURRENCE_DRIFT,
            lane_root,
            "command occurrence",
        )));
    }
    let produced = match produce_asset_transfer_fragment_v1(
        accepted,
        lane_root,
        prior_fragment,
        claimant_entitlements,
    ) {
        Ok(fragment) => fragment,
        Err(rejected) => {
            return Ok(Err(AssetTransferFragmentAdmissionRejectedV1::Producer(
                rejected,
            )))
        }
    };
    if produced.binding_root != journal.receipt_root {
        return Ok(Err(reject_witness(
            ReceiptWitnessRejectCodeV1::WITNESS_BINDING_ROOT_DRIFT,
            lane_root,
            "binding root",
        )));
    }
    Ok(Ok(VerifiedLaneAllocationFragmentV1 {
        fragment: produced,
        module_journal_root: witness.module_journal_root().clone(),
        receipt_root: journal.receipt_root.clone(),
        receipt_digest: witness.receipt_digest().clone(),
        expected_image_id: witness.expected_image_id().clone(),
        chain_id: journal.chain_id.clone(),
        deployment_root: journal.deployment_root.clone(),
        profile_root: journal.profile_root.clone(),
        writer_epoch: journal.writer_epoch,
    }))
}
