use std::{collections::HashSet, path::PathBuf};

#[derive(Debug)]
pub(super) struct ProveOptions {
    pub(super) v7_receipt_out: PathBuf,
    pub(super) v7_receipt_seal_mutation_out: PathBuf,
    pub(super) v7_journal_out: PathBuf,
    pub(super) v7_verifier_output_out: PathBuf,
    pub(super) v7_plan_b_out: PathBuf,
    pub(super) v6_child_receipt: PathBuf,
    pub(super) v7_guest_input: PathBuf,
}

#[derive(Debug)]
pub(super) struct ProfileOptions {
    pub(super) execution_profile_out: PathBuf,
    pub(super) v6_child_receipt: PathBuf,
    pub(super) v7_guest_input: PathBuf,
}

#[derive(Debug)]
pub(super) enum CommandV1 {
    Prove(ProveOptions),
    Profile(ProfileOptions),
}

const PROVE_USAGE: &str = "usage: prove_spot_settlement_v7 --v7-receipt-out <receipt.json> --v7-receipt-seal-mutation-out <mutation.json> --v7-journal-out <journal.bin> --v7-verifier-output-out <output.bin> --v7-plan-b-out <plan-b.bin> --v6-child-receipt <v6.receipt.json> --v7-guest-input <guest-input.bin>";
const PROFILE_USAGE: &str = "usage: prove_spot_settlement_v7 --profile-only --execution-profile-out <profile.json> --v6-child-receipt <v6.receipt.json> --v7-guest-input <guest-input.bin>";

pub(super) fn parse_options(args: impl IntoIterator<Item = String>) -> Result<CommandV1, String> {
    let args = args.into_iter().collect::<Vec<_>>();
    if args.first().map(String::as_str) == Some("--profile-only") {
        return parse_profile_options(&args);
    }
    parse_prove_options(&args).map(CommandV1::Prove)
}

fn parse_prove_options(args: &[String]) -> Result<ProveOptions, String> {
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
        return Err(PROVE_USAGE.to_owned());
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
    Ok(ProveOptions {
        v7_receipt_out: values[0].clone(),
        v7_receipt_seal_mutation_out: values[1].clone(),
        v7_journal_out: values[2].clone(),
        v7_verifier_output_out: values[3].clone(),
        v7_plan_b_out: values[4].clone(),
        v6_child_receipt: values[5].clone(),
        v7_guest_input: values[6].clone(),
    })
}

fn parse_profile_options(args: &[String]) -> Result<CommandV1, String> {
    let flags = [
        "--profile-only",
        "--execution-profile-out",
        "--v6-child-receipt",
        "--v7-guest-input",
    ];
    if args.len() != 7
        || args[0] != flags[0]
        || flags[1..]
            .iter()
            .enumerate()
            .any(|(index, flag)| args[1 + index * 2] != *flag)
        || (0..3).any(|index| {
            let value = &args[2 + index * 2];
            value.is_empty() || value.starts_with("--")
        })
    {
        return Err(PROFILE_USAGE.to_owned());
    }
    let execution_profile_out = PathBuf::from(&args[2]);
    let v6_child_receipt = PathBuf::from(&args[4]);
    let v7_guest_input = PathBuf::from(&args[6]);
    if execution_profile_out == v6_child_receipt || execution_profile_out == v7_guest_input {
        return Err("V7 execution-profile output must differ from every input".to_owned());
    }
    Ok(CommandV1::Profile(ProfileOptions {
        execution_profile_out,
        v6_child_receipt,
        v7_guest_input,
    }))
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
        let CommandV1::Prove(options) = parse_options(exact_args()).expect("exact CLI must parse")
        else {
            panic!("proof CLI selected wrong mode");
        };
        assert_eq!(options.v7_receipt_out, PathBuf::from("receipt.json"));
        assert_eq!(options.v7_guest_input, PathBuf::from("guest.bin"));
    }

    #[test]
    fn exact_profile_only_options_parse() {
        let args = [
            "--profile-only",
            "--execution-profile-out",
            "profile.json",
            "--v6-child-receipt",
            "child.json",
            "--v7-guest-input",
            "guest.bin",
        ]
        .map(str::to_owned);
        let CommandV1::Profile(options) = parse_options(args).expect("profile CLI must parse")
        else {
            panic!("profile CLI selected wrong mode");
        };
        assert_eq!(options.execution_profile_out, PathBuf::from("profile.json"));
        assert_eq!(options.v6_child_receipt, PathBuf::from("child.json"));
        assert_eq!(options.v7_guest_input, PathBuf::from("guest.bin"));
    }

    #[test]
    fn unknown_reordered_and_missing_options_reject() {
        let mut unknown = exact_args();
        unknown[0] = "--receipt".to_owned();
        assert_eq!(parse_options(unknown).unwrap_err(), PROVE_USAGE);

        let mut reordered = exact_args();
        reordered.swap(0, 2);
        assert_eq!(parse_options(reordered).unwrap_err(), PROVE_USAGE);

        let mut missing = exact_args();
        missing.pop();
        assert_eq!(parse_options(missing).unwrap_err(), PROVE_USAGE);
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

    #[test]
    fn malformed_or_aliased_profile_only_options_reject() {
        let exact = [
            "--profile-only",
            "--execution-profile-out",
            "profile.json",
            "--v6-child-receipt",
            "child.json",
            "--v7-guest-input",
            "guest.bin",
        ]
        .map(str::to_owned)
        .to_vec();

        let mut reordered = exact.clone();
        reordered.swap(1, 3);
        assert_eq!(parse_options(reordered).unwrap_err(), PROFILE_USAGE);

        let mut unknown = exact.clone();
        unknown[1] = "--profile-out".to_owned();
        assert_eq!(parse_options(unknown).unwrap_err(), PROFILE_USAGE);

        let mut alias = exact;
        alias[2] = "child.json".to_owned();
        assert!(parse_options(alias).is_err());
    }
}
