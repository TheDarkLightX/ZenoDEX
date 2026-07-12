use std::{env, path::PathBuf};

use zenodex_zrpf_protocol_v3::{CommitmentV3, NodeLevelV3, ProfileIdV3};
use zenodex_zrpf_risc0_verifier::ExpectedValueAggregateReceiptIdentityV5;

pub(super) const MAX_CHILDREN: usize = 8;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Mode {
    Prove,
    VerifyExisting,
}

impl Mode {
    pub(super) const fn as_str(self) -> &'static str {
        match self {
            Self::Prove => "prove",
            Self::VerifyExisting => "verify_existing",
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub(super) struct Options {
    pub(super) mode: Mode,
    pub(super) receipt_path: PathBuf,
    pub(super) expected_identity: ExpectedValueAggregateReceiptIdentityV5,
    pub(super) child_paths: Vec<PathBuf>,
}

pub(super) fn process_options() -> Result<Options, String> {
    let args = env::args_os()
        .skip(1)
        .map(|value| value.into_string().map_err(|_| usage().to_owned()))
        .collect::<Result<Vec<_>, _>>()?;
    parse_options(args)
}

pub(super) fn parse_options(args: Vec<String>) -> Result<Options, String> {
    let (mode, receipt_flag) = match args.first().map(String::as_str) {
        Some("prove") => (Mode::Prove, "--receipt-out"),
        Some("verify-existing") => (Mode::VerifyExisting, "--receipt"),
        _ => return Err(usage().to_owned()),
    };
    if args.len() < 9
        || args.get(1).map(String::as_str) != Some(receipt_flag)
        || args.get(3).map(String::as_str) != Some("--expected-proof-profile-id")
        || args.get(5).map(String::as_str) != Some("--expected-program-manifest-root")
    {
        return Err(usage().to_owned());
    }
    let receipt_path = required_path(args.get(2))?;
    let proof_profile_id =
        ProfileIdV3::new(parse_lower_hex32(args.get(4))?).map_err(|_| usage().to_owned())?;
    let program_manifest_root =
        CommitmentV3::new(parse_lower_hex32(args.get(6))?).map_err(|_| usage().to_owned())?;
    let child_paths = parse_child_paths(&args[7..])?;
    Ok(Options {
        mode,
        receipt_path,
        expected_identity: ExpectedValueAggregateReceiptIdentityV5::new(
            NodeLevelV3::new(1).map_err(|_| usage().to_owned())?,
            proof_profile_id,
            program_manifest_root,
        )
        .map_err(|_| usage().to_owned())?,
        child_paths,
    })
}

fn parse_child_paths(args: &[String]) -> Result<Vec<PathBuf>, String> {
    if !args.len().is_multiple_of(2) {
        return Err(usage().to_owned());
    }
    let mut paths = Vec::new();
    for pair in args.chunks_exact(2) {
        if pair[0] != "--child" || paths.len() == MAX_CHILDREN {
            return Err(usage().to_owned());
        }
        paths.push(required_path(pair.get(1))?);
    }
    if paths.is_empty() {
        return Err(usage().to_owned());
    }
    Ok(paths)
}

fn required_path(value: Option<&String>) -> Result<PathBuf, String> {
    value
        .filter(|candidate| !candidate.is_empty() && !candidate.starts_with("--"))
        .map(PathBuf::from)
        .ok_or_else(|| usage().to_owned())
}

fn parse_lower_hex32(value: Option<&String>) -> Result<[u8; 32], String> {
    let value = value.filter(|candidate| {
        candidate.len() == 64
            && candidate
                .bytes()
                .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    });
    let bytes =
        hex::decode(value.ok_or_else(|| usage().to_owned())?).map_err(|_| usage().to_owned())?;
    bytes.try_into().map_err(|_| usage().to_owned())
}

fn usage() -> &'static str {
    "usage: prove_value_aggregate_l1_v5 <prove --receipt-out|verify-existing --receipt> <receipt.json> --expected-proof-profile-id <lower-hex32> --expected-program-manifest-root <lower-hex32> --child <v4-receipt.json> [--child <v4-receipt.json> ...]"
}
