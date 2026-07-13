use std::{env, path::PathBuf};

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
    if args.len() < 5 || args.get(1).map(String::as_str) != Some(receipt_flag) {
        return Err(usage().to_owned());
    }
    let receipt_path = required_path(args.get(2))?;
    let child_paths = parse_child_paths(&args[3..])?;
    Ok(Options {
        mode,
        receipt_path,
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

fn usage() -> &'static str {
    "usage: prove_value_aggregate_l1_v5 <prove --receipt-out|verify-existing --receipt> <receipt.json> --child <v4-receipt.json> [--child <v4-receipt.json> ...]"
}
