pub const RECURSIVE_V2_LOCAL_NONCLAIMS: [&str; 7] = [
    "migration profile: the transition leaf still uses the authenticated v1 leaf journal",
    "the harness-local v1 image allowlist has no release or registry authority",
    "one-leaf smoke does not establish production throughput or proving-cost bounds",
    "this harness does not grant release, settlement, or ledger-admission authority",
    "schedule and data-availability fields remain commitment-only in this profile",
    "strict closed subtrees do not support cross-subtree value or message flows",
    "this local run does not establish cross-host reproducibility or privacy",
];

#[allow(dead_code)]
pub fn has_exact_recursive_v2_local_nonclaims(values: &[String]) -> bool {
    values
        .iter()
        .map(String::as_str)
        .eq(RECURSIVE_V2_LOCAL_NONCLAIMS)
}

#[cfg(test)]
mod tests {
    use super::{has_exact_recursive_v2_local_nonclaims, RECURSIVE_V2_LOCAL_NONCLAIMS};

    fn canonical() -> Vec<String> {
        RECURSIVE_V2_LOCAL_NONCLAIMS
            .iter()
            .map(|value| (*value).to_string())
            .collect()
    }

    #[test]
    fn exact_nonclaim_policy_accepts() {
        assert!(has_exact_recursive_v2_local_nonclaims(&canonical()));
    }

    #[test]
    fn weakened_reordered_or_extended_nonclaim_policy_rejects() {
        let mut weakened = canonical();
        weakened[0] = "experimental".to_string();
        assert!(!has_exact_recursive_v2_local_nonclaims(&weakened));

        let mut reordered = canonical();
        reordered.swap(0, 1);
        assert!(!has_exact_recursive_v2_local_nonclaims(&reordered));

        let mut extended = canonical();
        extended.push("extra".to_string());
        assert!(!has_exact_recursive_v2_local_nonclaims(&extended));
    }
}
