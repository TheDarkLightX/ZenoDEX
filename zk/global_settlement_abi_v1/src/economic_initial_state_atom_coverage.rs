//! Canonical source classification for explicit initial-state value rows.

use serde::{Deserialize, Serialize};

use crate::canonical::{
    hash_global_v1, validate_schema_v1, AbiErrorV1, AbiResultV1, RootV1, GLOBAL_SETTLEMENT_ABI_V1,
};
use crate::economic_initial_state::EconomicInitialStateKindV1;
use crate::release::{
    EconomicPolicyBindingV1, EconomicPolicyRegistryV1, EconomicProfileSnapshotV1,
};
use crate::state::GlobalEconomicStateV1;

pub const MAX_INITIAL_STATE_ATOM_ROWS_V1: usize = 4_096;
pub const M6_INITIAL_STATE_ATOM_COVERAGE_POLICY_KIND_V1: &str = "m6_initial_state_atom_coverage_v1";
pub const M6_INITIAL_STATE_ATOM_COVERAGE_PROFILE_COMMAND_KIND_V1: &str =
    "global_economic_profile_v1";

#[derive(Clone, Copy, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(rename_all = "SCREAMING_SNAKE_CASE")]
pub enum EconomicInitialStateAtomKindV1 {
    Balance,
    Supply,
    Custody,
    Liability,
    Reserve,
    TerminalObligation,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "SCREAMING_SNAKE_CASE")]
pub enum EconomicInitialStateAtomClassificationV1 {
    GenesisAllocation,
    MigratedTarget,
    RetainedDrainTarget,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct EconomicInitialStateAtomOccurrenceV1 {
    pub atom_kind: EconomicInitialStateAtomKindV1,
    pub state_row_index: u64,
    pub row_root: RootV1,
}

impl EconomicInitialStateAtomOccurrenceV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        self.row_root.validate("initial state atom row root", false)
    }

    fn order_key(&self) -> (EconomicInitialStateAtomKindV1, u64) {
        (self.atom_kind, self.state_row_index)
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct EconomicInitialStateAtomSourceV1 {
    pub occurrence: EconomicInitialStateAtomOccurrenceV1,
    pub classification: EconomicInitialStateAtomClassificationV1,
    pub source_authorization_root: RootV1,
}

impl EconomicInitialStateAtomSourceV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        self.occurrence.validate()?;
        self.source_authorization_root
            .validate("initial state atom source authorization root", false)
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct EconomicInitialStateSourceManifestV1 {
    pub schema: String,
    pub kind: EconomicInitialStateKindV1,
    pub rows: Vec<EconomicInitialStateAtomSourceV1>,
}

impl EconomicInitialStateSourceManifestV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        validate_schema_v1(&self.schema)?;
        if self.rows.len() > MAX_INITIAL_STATE_ATOM_ROWS_V1 {
            return Err(AbiErrorV1::InvalidBounds(
                "initial state source manifest rows",
            ));
        }
        for row in &self.rows {
            row.validate()?;
        }
        if self
            .rows
            .windows(2)
            .any(|pair| pair[0].occurrence.order_key() >= pair[1].occurrence.order_key())
        {
            return Err(AbiErrorV1::InvalidOrder(
                "initial state source manifest rows",
            ));
        }
        let classifications_match = self.rows.iter().all(|row| match self.kind {
            EconomicInitialStateKindV1::GENESIS => {
                row.classification == EconomicInitialStateAtomClassificationV1::GenesisAllocation
            }
            EconomicInitialStateKindV1::MIGRATION => matches!(
                row.classification,
                EconomicInitialStateAtomClassificationV1::MigratedTarget
                    | EconomicInitialStateAtomClassificationV1::RetainedDrainTarget
            ),
        });
        if !classifications_match {
            return Err(AbiErrorV1::InvalidBinding(
                "initial state source manifest classification",
            ));
        }
        Ok(())
    }

    pub fn manifest_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1("economic-initial-state-atom-coverage-v1", self)
    }
}

#[derive(Serialize)]
struct EconomicInitialStateAtomRowV1<'a, T: Serialize> {
    schema: &'static str,
    atom_kind: EconomicInitialStateAtomKindV1,
    state_row_index: u64,
    row: &'a T,
}

fn occurrence_v1<T: Serialize>(
    atom_kind: EconomicInitialStateAtomKindV1,
    state_row_index: usize,
    row: &T,
) -> AbiResultV1<EconomicInitialStateAtomOccurrenceV1> {
    let state_row_index = u64::try_from(state_row_index)
        .map_err(|_| AbiErrorV1::InvalidBounds("initial state atom row index"))?;
    let canonical_row = EconomicInitialStateAtomRowV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1,
        atom_kind,
        state_row_index,
        row,
    };
    Ok(EconomicInitialStateAtomOccurrenceV1 {
        atom_kind,
        state_row_index,
        row_root: hash_global_v1("economic-initial-state-atom-row-v1", &canonical_row)?,
    })
}

fn extend_occurrences_v1<T: Serialize>(
    occurrences: &mut Vec<EconomicInitialStateAtomOccurrenceV1>,
    atom_kind: EconomicInitialStateAtomKindV1,
    rows: &[T],
) -> AbiResultV1<()> {
    for (state_row_index, row) in rows.iter().enumerate() {
        occurrences.push(occurrence_v1(atom_kind, state_row_index, row)?);
    }
    Ok(())
}

pub fn validate_economic_initial_state_explicit_row_count_v1(
    state: &GlobalEconomicStateV1,
) -> AbiResultV1<usize> {
    let explicit_row_count = [
        state.balances.len(),
        state.supplies.len(),
        state.custody.len(),
        state.liabilities.len(),
        state.reserves.len(),
        state.terminal_obligations.len(),
    ]
    .into_iter()
    .try_fold(0_usize, |total, count| total.checked_add(count))
    .ok_or(AbiErrorV1::InvalidBounds(
        "initial state explicit value rows",
    ))?;
    if explicit_row_count > MAX_INITIAL_STATE_ATOM_ROWS_V1 {
        return Err(AbiErrorV1::InvalidBounds(
            "initial state explicit value rows",
        ));
    }
    Ok(explicit_row_count)
}

pub fn derive_economic_initial_state_atom_occurrences_v1(
    state: &GlobalEconomicStateV1,
) -> AbiResultV1<Vec<EconomicInitialStateAtomOccurrenceV1>> {
    let explicit_row_count = validate_economic_initial_state_explicit_row_count_v1(state)?;
    state.validate()?;
    let mut occurrences = Vec::with_capacity(explicit_row_count);
    extend_occurrences_v1(
        &mut occurrences,
        EconomicInitialStateAtomKindV1::Balance,
        &state.balances,
    )?;
    extend_occurrences_v1(
        &mut occurrences,
        EconomicInitialStateAtomKindV1::Supply,
        &state.supplies,
    )?;
    extend_occurrences_v1(
        &mut occurrences,
        EconomicInitialStateAtomKindV1::Custody,
        &state.custody,
    )?;
    extend_occurrences_v1(
        &mut occurrences,
        EconomicInitialStateAtomKindV1::Liability,
        &state.liabilities,
    )?;
    extend_occurrences_v1(
        &mut occurrences,
        EconomicInitialStateAtomKindV1::Reserve,
        &state.reserves,
    )?;
    extend_occurrences_v1(
        &mut occurrences,
        EconomicInitialStateAtomKindV1::TerminalObligation,
        &state.terminal_obligations,
    )?;
    Ok(occurrences)
}

pub fn validate_economic_initial_state_atom_coverage_v1(
    state: &GlobalEconomicStateV1,
    source_manifest: &EconomicInitialStateSourceManifestV1,
) -> AbiResultV1<RootV1> {
    source_manifest.validate()?;
    let expected = derive_economic_initial_state_atom_occurrences_v1(state)?;
    let actual: Vec<_> = source_manifest
        .rows
        .iter()
        .map(|row| row.occurrence.clone())
        .collect();
    if actual != expected {
        return Err(AbiErrorV1::InvalidBinding(
            "initial state atom target coverage",
        ));
    }
    source_manifest.manifest_root()
}

pub fn economic_initial_state_atom_coverage_policy_binding_v1(
    source_manifest: &EconomicInitialStateSourceManifestV1,
) -> AbiResultV1<EconomicPolicyBindingV1> {
    Ok(EconomicPolicyBindingV1 {
        policy_kind: M6_INITIAL_STATE_ATOM_COVERAGE_POLICY_KIND_V1.to_owned(),
        command_kind: M6_INITIAL_STATE_ATOM_COVERAGE_PROFILE_COMMAND_KIND_V1.to_owned(),
        policy_root: source_manifest.manifest_root()?,
    })
}

pub fn validate_economic_initial_state_atom_coverage_profile_binding_v1(
    profile: &EconomicProfileSnapshotV1,
    policy_registry: &EconomicPolicyRegistryV1,
    source_manifest: &EconomicInitialStateSourceManifestV1,
) -> AbiResultV1<()> {
    profile.validate()?;
    if policy_registry.registry_root()? != profile.policy_registry_root {
        return Err(AbiErrorV1::InvalidBinding(
            "initial state coverage policy registry root",
        ));
    }
    let binding = policy_registry.require_binding(
        M6_INITIAL_STATE_ATOM_COVERAGE_POLICY_KIND_V1,
        M6_INITIAL_STATE_ATOM_COVERAGE_PROFILE_COMMAND_KIND_V1,
    )?;
    if binding.policy_root != source_manifest.manifest_root()? {
        return Err(AbiErrorV1::InvalidBinding(
            "initial state atom coverage manifest root",
        ));
    }
    Ok(())
}
