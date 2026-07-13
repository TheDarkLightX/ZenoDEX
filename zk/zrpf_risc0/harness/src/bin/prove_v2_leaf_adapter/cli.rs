use std::path::PathBuf;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Mode {
    Prove,
    VerifyReceipt,
    MissingAssumption,
    SubstitutedSourceJournal,
}

#[derive(Debug, PartialEq, Eq)]
pub(super) struct Options {
    pub(super) source_proof: PathBuf,
    pub(super) receipt_path: Option<PathBuf>,
    pub(super) assigned_leaf_ordinal: u64,
    pub(super) mode: Mode,
}

pub(super) fn usage() -> &'static str {
    "usage: prove_v2_leaf_adapter --source-proof <source.proof.json> (--receipt-out <adapter.receipt.json>|--verify-receipt <adapter.receipt.json>|--missing-assumption|--substituted-source-journal) [--ordinal <canonical-u64>]"
}

pub(super) fn parse_options(args: impl IntoIterator<Item = String>) -> Result<Options, String> {
    let args = args.into_iter().collect::<Vec<_>>();
    if args.len() < 3
        || args.len() > 6
        || args[0] != "--source-proof"
        || args[1].is_empty()
        || args[1].starts_with("--")
    {
        return Err(usage().to_owned());
    }
    let source_proof = PathBuf::from(&args[1]);
    let (mode, receipt_path, consumed) = parse_mode(&args)?;
    let assigned_leaf_ordinal = match args.get(consumed..) {
        Some([]) => 0,
        Some([flag, value]) if flag == "--ordinal" => parse_canonical_ordinal(value)?,
        _ => return Err(usage().to_owned()),
    };
    if receipt_path
        .as_ref()
        .is_some_and(|path| path == &source_proof)
    {
        return Err("source proof and adapter receipt paths must differ".to_owned());
    }
    Ok(Options {
        source_proof,
        receipt_path,
        assigned_leaf_ordinal,
        mode,
    })
}

fn parse_mode(args: &[String]) -> Result<(Mode, Option<PathBuf>, usize), String> {
    match args[2].as_str() {
        "--receipt-out" | "--verify-receipt"
            if args.len() >= 4 && !args[3].is_empty() && !args[3].starts_with("--") =>
        {
            let mode = if args[2] == "--receipt-out" {
                Mode::Prove
            } else {
                Mode::VerifyReceipt
            };
            Ok((mode, Some(PathBuf::from(&args[3])), 4))
        }
        "--missing-assumption" => Ok((Mode::MissingAssumption, None, 3)),
        "--substituted-source-journal" => Ok((Mode::SubstitutedSourceJournal, None, 3)),
        _ => Err(usage().to_owned()),
    }
}

fn parse_canonical_ordinal(value: &str) -> Result<u64, String> {
    let parsed = value
        .parse::<u64>()
        .map_err(|_| "ordinal must be a canonical unsigned integer".to_owned())?;
    if value != parsed.to_string() {
        return Err("ordinal must be a canonical unsigned integer".to_owned());
    }
    parsed
        .checked_add(1)
        .ok_or_else(|| "ordinal must leave room for one leaf".to_owned())?;
    Ok(parsed)
}
