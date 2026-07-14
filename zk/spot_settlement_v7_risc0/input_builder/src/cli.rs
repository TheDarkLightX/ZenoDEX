use std::ffi::{OsStr, OsString};
use std::path::{Path, PathBuf};

use zenodex_zrpf_protocol_v3::{
    MAX_FULL_BLOB_DA_CERTIFICATE_BYTES_V1, MAX_SETTLEMENT_ADMISSION_JOURNAL_BYTES_V1,
};
use zenodex_zrpf_risc0_spot_settlement_v6_shared::MAX_SOURCE_OPENED_SPOT_SETTLEMENT_REPLAY_BYTES_V3;
use zenodex_zrpf_risc0_spot_state_root_v7_semantic_shared::MAX_SPOT_STATE_ROOT_V7_HOST_INPUT_BYTES_V1;

use crate::artifact_io::{persist_create_new_exact_v1, read_stable_bounded_input_v1};
use crate::{
    build_canonical_spot_settlement_v7_guest_input_v1, SpotSettlementV7InputBuilderErrorV1,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SpotSettlementV7InputBuilderPathsV1 {
    source_child_journal: PathBuf,
    data_availability_certificate: PathBuf,
    replay: PathBuf,
    state_root_host_input: PathBuf,
    output: PathBuf,
}

impl SpotSettlementV7InputBuilderPathsV1 {
    pub fn source_child_journal(&self) -> &Path {
        &self.source_child_journal
    }

    pub fn data_availability_certificate(&self) -> &Path {
        &self.data_availability_certificate
    }

    pub fn replay(&self) -> &Path {
        &self.replay
    }

    pub fn state_root_host_input(&self) -> &Path {
        &self.state_root_host_input
    }

    pub fn output(&self) -> &Path {
        &self.output
    }
}

#[derive(Default)]
struct PartialPathsV1 {
    source_child_journal: Option<PathBuf>,
    data_availability_certificate: Option<PathBuf>,
    replay: Option<PathBuf>,
    state_root_host_input: Option<PathBuf>,
    output: Option<PathBuf>,
}

pub fn parse_spot_settlement_v7_input_builder_args_v1<I, T>(
    args: I,
) -> Result<SpotSettlementV7InputBuilderPathsV1, SpotSettlementV7InputBuilderErrorV1>
where
    I: IntoIterator<Item = T>,
    T: Into<OsString>,
{
    let mut iterator = args.into_iter().map(Into::into);
    let mut partial = PartialPathsV1::default();
    while let Some(flag) = iterator.next() {
        let (label, slot) = option_slot(&mut partial, &flag)?;
        if slot.is_some() {
            return Err(SpotSettlementV7InputBuilderErrorV1::DuplicateOption(label));
        }
        let value =
            iterator
                .next()
                .ok_or(SpotSettlementV7InputBuilderErrorV1::MissingOptionValue(
                    label,
                ))?;
        *slot = Some(PathBuf::from(value));
    }
    Ok(SpotSettlementV7InputBuilderPathsV1 {
        source_child_journal: require_option(partial.source_child_journal, "source child journal")?,
        data_availability_certificate: require_option(
            partial.data_availability_certificate,
            "data availability certificate",
        )?,
        replay: require_option(partial.replay, "source replay")?,
        state_root_host_input: require_option(
            partial.state_root_host_input,
            "state-root host input",
        )?,
        output: require_option(partial.output, "output")?,
    })
}

pub fn run_spot_settlement_v7_input_builder_v1(
    paths: &SpotSettlementV7InputBuilderPathsV1,
) -> Result<(), SpotSettlementV7InputBuilderErrorV1> {
    let source_child_journal = read_stable_bounded_input_v1(
        paths.source_child_journal(),
        MAX_SETTLEMENT_ADMISSION_JOURNAL_BYTES_V1,
        "source child journal",
    )?;
    let data_availability_certificate = read_stable_bounded_input_v1(
        paths.data_availability_certificate(),
        MAX_FULL_BLOB_DA_CERTIFICATE_BYTES_V1,
        "data availability certificate",
    )?;
    let replay = read_stable_bounded_input_v1(
        paths.replay(),
        MAX_SOURCE_OPENED_SPOT_SETTLEMENT_REPLAY_BYTES_V3,
        "source replay",
    )?;
    let state_root_host_input = read_stable_bounded_input_v1(
        paths.state_root_host_input(),
        MAX_SPOT_STATE_ROOT_V7_HOST_INPUT_BYTES_V1,
        "state-root host input",
    )?;
    let guest_input = build_canonical_spot_settlement_v7_guest_input_v1(
        &source_child_journal,
        &data_availability_certificate,
        &replay,
        &state_root_host_input,
    )?;
    persist_create_new_exact_v1(paths.output(), &guest_input)
}

fn option_slot<'a>(
    partial: &'a mut PartialPathsV1,
    flag: &OsStr,
) -> Result<(&'static str, &'a mut Option<PathBuf>), SpotSettlementV7InputBuilderErrorV1> {
    if flag == "--source-child-journal" {
        Ok(("source child journal", &mut partial.source_child_journal))
    } else if flag == "--data-availability-certificate" {
        Ok((
            "data availability certificate",
            &mut partial.data_availability_certificate,
        ))
    } else if flag == "--replay" {
        Ok(("source replay", &mut partial.replay))
    } else if flag == "--state-root-host-input" {
        Ok(("state-root host input", &mut partial.state_root_host_input))
    } else if flag == "--output" {
        Ok(("output", &mut partial.output))
    } else {
        Err(SpotSettlementV7InputBuilderErrorV1::UnknownOption)
    }
}

fn require_option(
    value: Option<PathBuf>,
    label: &'static str,
) -> Result<PathBuf, SpotSettlementV7InputBuilderErrorV1> {
    value.ok_or(SpotSettlementV7InputBuilderErrorV1::MissingOption(label))
}
