use std::{env, path::PathBuf};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Mode {
    Preflight,
    Prove,
}

impl Mode {
    pub(super) const fn as_str(self) -> &'static str {
        match self {
            Self::Preflight => "preflight",
            Self::Prove => "prove",
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub(super) struct Options {
    pub(super) mode: Mode,
    pub(super) level_one_program: PathBuf,
    pub(super) level_two_program: PathBuf,
    pub(super) child_receipt: PathBuf,
    pub(super) bundle_out: Option<PathBuf>,
}

pub(super) fn process_options() -> Result<Options, String> {
    let arguments = env::args_os()
        .skip(1)
        .map(|value| value.into_string().map_err(|_| usage().to_owned()))
        .collect::<Result<Vec<_>, _>>()?;
    parse_options(arguments)
}

pub(super) fn parse_options(arguments: Vec<String>) -> Result<Options, String> {
    let mode = match arguments.first().map(String::as_str) {
        Some("preflight") => Mode::Preflight,
        Some("prove") => Mode::Prove,
        _ => return Err(usage().to_owned()),
    };
    let mut level_one_program = None;
    let mut level_two_program = None;
    let mut child_receipt = None;
    let mut bundle_out = None;
    let fields = arguments.get(1..).ok_or_else(|| usage().to_owned())?;
    if !fields.len().is_multiple_of(2) {
        return Err(usage().to_owned());
    }
    for pair in fields.chunks_exact(2) {
        let value = required_path(pair.get(1))?;
        match pair[0].as_str() {
            "--level-one-program" if level_one_program.is_none() => level_one_program = Some(value),
            "--level-two-program" if level_two_program.is_none() => level_two_program = Some(value),
            "--child-receipt" if child_receipt.is_none() => child_receipt = Some(value),
            "--bundle-out" if bundle_out.is_none() => bundle_out = Some(value),
            _ => return Err(usage().to_owned()),
        }
    }
    if mode == Mode::Preflight && bundle_out.is_some() {
        return Err(usage().to_owned());
    }
    if mode == Mode::Prove && bundle_out.is_none() {
        return Err(usage().to_owned());
    }
    Ok(Options {
        mode,
        level_one_program: level_one_program.ok_or_else(|| usage().to_owned())?,
        level_two_program: level_two_program.ok_or_else(|| usage().to_owned())?,
        child_receipt: child_receipt.ok_or_else(|| usage().to_owned())?,
        bundle_out,
    })
}

fn required_path(value: Option<&String>) -> Result<PathBuf, String> {
    value
        .filter(|candidate| !candidate.is_empty() && !candidate.starts_with("--"))
        .map(PathBuf::from)
        .ok_or_else(|| usage().to_owned())
}

fn usage() -> &'static str {
    "usage: prove_retained_value_aggregate_v5 <preflight|prove> \
--level-one-program <value-aggregate-l1.combined.bin> \
--level-two-program <value-aggregate-l2.combined.bin> \
--child-receipt <compatible-v4.receipt.json> \
[--bundle-out <v5-receipt-bundle.json>]"
}
