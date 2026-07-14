use std::{collections::HashSet, path::PathBuf};

#[derive(Debug)]
pub(super) struct Options {
    pub(super) v7_receipt_out: PathBuf,
    pub(super) v7_receipt_seal_mutation_out: PathBuf,
    pub(super) v7_journal_out: PathBuf,
    pub(super) v7_verifier_output_out: PathBuf,
    pub(super) v7_plan_b_out: PathBuf,
    pub(super) v6_child_receipt: PathBuf,
    pub(super) v7_guest_input: PathBuf,
}

const USAGE: &str = "usage: prove_spot_settlement_v7 --v7-receipt-out <receipt.json> --v7-receipt-seal-mutation-out <mutation.json> --v7-journal-out <journal.bin> --v7-verifier-output-out <output.bin> --v7-plan-b-out <plan-b.bin> --v6-child-receipt <v6.receipt.json> --v7-guest-input <guest-input.bin>";

pub(super) fn parse_options(args: impl IntoIterator<Item = String>) -> Result<Options, String> {
    let args = args.into_iter().collect::<Vec<_>>();
    let flags = [
        "--v7-receipt-out",
        "--v7-receipt-seal-mutation-out",
        "--v7-journal-out",
        "--v7-verifier-output-out",
        "--v7-plan-b-out",
        "--v6-child-receipt",
        "--v7-guest-input",
    ];
    if args.len() != flags.len() * 2
        || flags
            .iter()
            .enumerate()
            .any(|(index, flag)| args[index * 2] != *flag)
        || (0..flags.len()).any(|index| {
            let value = &args[index * 2 + 1];
            value.is_empty() || value.starts_with("--")
        })
    {
        return Err(USAGE.to_owned());
    }
    let values = (0..flags.len())
        .map(|index| PathBuf::from(&args[index * 2 + 1]))
        .collect::<Vec<_>>();
    let output_paths = values[..5].iter().collect::<HashSet<_>>();
    if output_paths.len() != 5
        || values[..5]
            .iter()
            .any(|output| output == &values[5] || output == &values[6])
    {
        return Err("V7 artifact output paths must be distinct from every input".to_owned());
    }
    Ok(Options {
        v7_receipt_out: values[0].clone(),
        v7_receipt_seal_mutation_out: values[1].clone(),
        v7_journal_out: values[2].clone(),
        v7_verifier_output_out: values[3].clone(),
        v7_plan_b_out: values[4].clone(),
        v6_child_receipt: values[5].clone(),
        v7_guest_input: values[6].clone(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn exact_args() -> Vec<String> {
        [
            "--v7-receipt-out",
            "receipt.json",
            "--v7-receipt-seal-mutation-out",
            "mutation.json",
            "--v7-journal-out",
            "journal.bin",
            "--v7-verifier-output-out",
            "output.bin",
            "--v7-plan-b-out",
            "plan.bin",
            "--v6-child-receipt",
            "child.json",
            "--v7-guest-input",
            "guest.bin",
        ]
        .map(str::to_owned)
        .to_vec()
    }

    #[test]
    fn exact_ordered_options_parse() {
        let options = parse_options(exact_args()).expect("exact CLI must parse");
        assert_eq!(options.v7_receipt_out, PathBuf::from("receipt.json"));
        assert_eq!(options.v7_guest_input, PathBuf::from("guest.bin"));
    }

    #[test]
    fn unknown_reordered_and_missing_options_reject() {
        let mut unknown = exact_args();
        unknown[0] = "--receipt".to_owned();
        assert_eq!(parse_options(unknown).unwrap_err(), USAGE);

        let mut reordered = exact_args();
        reordered.swap(0, 2);
        assert_eq!(parse_options(reordered).unwrap_err(), USAGE);

        let mut missing = exact_args();
        missing.pop();
        assert_eq!(parse_options(missing).unwrap_err(), USAGE);
    }

    #[test]
    fn aliased_output_and_input_paths_reject() {
        let mut output_alias = exact_args();
        output_alias[3] = "receipt.json".to_owned();
        assert!(parse_options(output_alias).is_err());

        let mut input_alias = exact_args();
        input_alias[11] = "receipt.json".to_owned();
        assert!(parse_options(input_alias).is_err());
    }
}
