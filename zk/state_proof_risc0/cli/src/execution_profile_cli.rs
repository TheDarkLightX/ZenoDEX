use std::path::PathBuf;

const PROFILE_USAGE: &str = "usage: tau-state-proof-risc0-cli --profile-recursive-spot-leaf --execution-profile-out <profile.json> --guest-input-out <guest-input.bin>";

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RecursiveSpotLeafProfileOptionsV1 {
    pub execution_profile_out: PathBuf,
    pub guest_input_out: PathBuf,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CommandV1 {
    Default,
    ProfileRecursiveSpotLeaf(RecursiveSpotLeafProfileOptionsV1),
}

pub fn parse_options(arguments: impl IntoIterator<Item = String>) -> Result<CommandV1, String> {
    let arguments = arguments.into_iter().collect::<Vec<_>>();
    if arguments.is_empty() {
        return Ok(CommandV1::Default);
    }
    let [mode, profile_flag, profile_path, input_flag, input_path] = arguments.as_slice() else {
        return Err(PROFILE_USAGE.to_owned());
    };
    if mode != "--profile-recursive-spot-leaf"
        || profile_flag != "--execution-profile-out"
        || input_flag != "--guest-input-out"
    {
        return Err(PROFILE_USAGE.to_owned());
    }
    let execution_profile_out = bounded_absolute_path(profile_path, "execution profile")?;
    let guest_input_out = bounded_absolute_path(input_path, "guest input")?;
    if execution_profile_out == guest_input_out {
        return Err("execution profile and guest input paths must be distinct".to_owned());
    }
    Ok(CommandV1::ProfileRecursiveSpotLeaf(
        RecursiveSpotLeafProfileOptionsV1 {
            execution_profile_out,
            guest_input_out,
        },
    ))
}

fn bounded_absolute_path(value: &str, label: &str) -> Result<PathBuf, String> {
    if value.is_empty() || value.len() > 4096 || value.contains('\0') {
        return Err(format!("{label} path is empty or oversized"));
    }
    let path = PathBuf::from(value);
    if !path.is_absolute() {
        return Err(format!("{label} path must be absolute"));
    }
    Ok(path)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_arguments_preserve_default_cli() {
        assert_eq!(parse_options(Vec::new()).unwrap(), CommandV1::Default);
    }

    #[test]
    fn profile_arguments_are_exact_and_position_distinct() {
        let parsed = parse_options(
            [
                "--profile-recursive-spot-leaf",
                "--execution-profile-out",
                "/tmp/non-palindromic-profile-17.json",
                "--guest-input-out",
                "/tmp/position-distinct-input-29.bin",
            ]
            .map(str::to_owned),
        )
        .unwrap();
        assert_eq!(
            parsed,
            CommandV1::ProfileRecursiveSpotLeaf(RecursiveSpotLeafProfileOptionsV1 {
                execution_profile_out: PathBuf::from("/tmp/non-palindromic-profile-17.json"),
                guest_input_out: PathBuf::from("/tmp/position-distinct-input-29.bin"),
            })
        );
    }

    #[test]
    fn reordered_missing_relative_and_aliased_arguments_reject() {
        for arguments in [
            vec!["--profile-recursive-spot-leaf"],
            vec![
                "--profile-recursive-spot-leaf",
                "--guest-input-out",
                "/tmp/input.bin",
                "--execution-profile-out",
                "/tmp/profile.json",
            ],
            vec![
                "--profile-recursive-spot-leaf",
                "--execution-profile-out",
                "relative.json",
                "--guest-input-out",
                "/tmp/input.bin",
            ],
            vec![
                "--profile-recursive-spot-leaf",
                "--execution-profile-out",
                "/tmp/same",
                "--guest-input-out",
                "/tmp/same",
            ],
        ] {
            assert!(parse_options(arguments.into_iter().map(str::to_owned)).is_err());
        }
    }
}
