//! Public claim-scope guard for release-bundle docs.
//!
//! The Python checker remains the release entrypoint, but this Rust mirror covers
//! the same release-facing docs that carry scoped `production_security_claim`
//! language. It deliberately uses simple text/anchor rules instead of importing a
//! YAML/regex stack into the runtime CLI crate.

use serde::Serialize;
use std::path::Path;

const SCHEMA: &str = "zenodex/public_claim_scope_report/rust-v0";

const REQUIRED_PATHS: &[&str] = &[
    "README.md",
    "docs/claims_registry.yaml",
    "docs/ASSURANCE_RELEASE_SNAPSHOT.md",
    "docs/PUBLIC_ASSURANCE_REPLAY.md",
    "docs/LOCAL_TESTNET_QUICKSTART.md",
    "docs/RC1_READINESS.md",
    "docs/RC1_SCOPE.md",
    "docs/RC1_VERIFIED_SURFACE_MATRIX.md",
    "docs/DEX_SURFACE_STATUS_2026_06_03.md",
    "docs/PERPS_NP_TESTNET_STATUS.md",
    "docs/RISC0_RELEASE_BINARY_ARTIFACTS_2026_06_02.md",
    "docs/zenodex_perps_np_state_proof_risc0_v1.md",
    "docs/zenodex_zusd_state_proof_risc0_v1.md",
    "docs/zenodex_spot_state_proof_risc0_v1.md",
    "docs/CONFIDENTIAL_EXTENSIONS_TEE_SMPC.md",
    "docs/CONFIDENTIAL_FEATURES_BETA_RUNBOOK.md",
    "docs/CONFIDENTIAL_FEATURES_USE_CASES.md",
    "docs/SPECIFICATION.md",
    "tools/dex-ui/README.md",
    "tools/dex-ui/src/lib/confidentialData.js",
    "src/integration/confidential_feature_status.py",
];

const OPTIONAL_PATHS: &[&str] = &[
    "docs/UPBA_OPTIMALITY_CERTIFICATE.md",
    "docs/UPBA_V1_CERTIFICATE.md",
    "docs/UPBA_V1_EVIDENCE_BOUNDARY.md",
    "docs/UPBA_V2_CERTIFICATE.md",
    "docs/UPBA_V2_EVIDENCE_BOUNDARY.md",
    "docs/ZENOCOVER_LP_LOSS_COVER_V1.md",
];

const REQUIRED_ANCHORS: &[(&str, &[&str])] = &[
    (
        "README.md",
        &[
            "The current UPBA work is scoped:",
            "UPBA reduces intra-batch ordering MEV. By itself it does not address",
            "This is current local evidence for the restricted guest path.",
            "It does not yet prove the full Python ZenoDEX runtime",
        ],
    ),
    (
        "docs/LOCAL_TESTNET_QUICKSTART.md",
        &[
            "local proof-wrapper gate for non-production development",
            "local-testnet fixture and sets `production_security_claim=false`",
        ],
    ),
    (
        "docs/DEX_SURFACE_STATUS_2026_06_03.md",
        &[
            "Product/testnet production posture: `production_security_claim = false`",
            "spot-DEX CBC authority-surface closure",
        ],
    ),
    (
        "docs/PERPS_NP_TESTNET_STATUS.md",
        &[
            "Perps NP / fake-value testnet",
            "spot-DEX CBC",
            "authority-surface matrix",
        ],
    ),
    (
        "docs/RISC0_RELEASE_BINARY_ARTIFACTS_2026_06_02.md",
        &[
            "claim_scope: scoped RISC0 transition binary artifacts only",
            "separate from the spot-DEX CBC authority-surface matrix",
        ],
    ),
    (
        "docs/zenodex_perps_np_state_proof_risc0_v1.md",
        &[
            "Transition Semantics (v1 Scope)",
            "`production_security_claim` for this proof surface remains `false`",
        ],
    ),
    (
        "docs/zenodex_zusd_state_proof_risc0_v1.md",
        &[
            "Transition Semantics (v1 Scope)",
            "`production_security_claim` for this proof surface remains `false`",
        ],
    ),
    (
        "docs/zenodex_spot_state_proof_risc0_v1.md",
        &["Transition semantics (v1 scope)", "Planned v2 extensions:"],
    ),
    (
        "docs/CONFIDENTIAL_FEATURES_BETA_RUNBOOK.md",
        &["This beta covers:", "It does not claim:"],
    ),
    (
        "docs/CONFIDENTIAL_FEATURES_USE_CASES.md",
        &[
            "What this does not promise",
            "It does not make everything private on-chain.",
            "It does not eliminate all trust.",
        ],
    ),
    (
        "tools/dex-ui/README.md",
        &[
            "Confidential exposes live operator posture through `GET /api/confidential/status`",
            "It is not the default swap path",
        ],
    ),
    (
        "tools/dex-ui/src/lib/confidentialData.js",
        &["No in-repo proof of TEE hardware confidentiality"],
    ),
    (
        "src/integration/confidential_feature_status.py",
        &["no in-repo proof of TEE hardware confidentiality"],
    ),
    (
        "docs/UPBA_V2_CERTIFICATE.md",
        &[
            "Still excluded:",
            "Completeness of the audited set remains a separate obligation",
        ],
    ),
    (
        "docs/UPBA_V2_EVIDENCE_BOUNDARY.md",
        &[
            "UPBA v2 does not currently claim:",
            "The v2 claim is narrower:",
        ],
    ),
    (
        "docs/ZENOCOVER_LP_LOSS_COVER_V1.md",
        &[
            "Legal and Regulatory Boundary",
            "This replay artifact is not a product launch",
            "Any public or production ZenoCover offering must complete counsel-led",
        ],
    ),
];

#[derive(Debug, Clone, Serialize, PartialEq, Eq)]
pub struct ClaimViolation {
    pub path: String,
    pub line: u32,
    pub rule_id: String,
    pub message: String,
    pub text: String,
}

#[derive(Debug, Clone, Serialize, PartialEq, Eq)]
pub struct ClaimScopeReport {
    pub schema: &'static str,
    pub ok: bool,
    pub checked_files: Vec<String>,
    pub violations: Vec<ClaimViolation>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct RuleHit {
    rule_id: &'static str,
    message: &'static str,
    match_start: usize,
}

pub fn check_root(root: &Path) -> Result<ClaimScopeReport, String> {
    let mut checked_files = Vec::new();
    let mut violations = Vec::new();

    for rel_path in REQUIRED_PATHS {
        let path = root.join(rel_path);
        if !path.is_file() {
            violations.push(ClaimViolation {
                path: (*rel_path).to_string(),
                line: 0,
                rule_id: "missing_public_claim_file".to_string(),
                message: "Public claim file is missing.".to_string(),
                text: String::new(),
            });
            continue;
        }
        let text = read_public_claim_file(&path)?;
        checked_files.push((*rel_path).to_string());
        violations.extend(check_required_anchors(rel_path, &text));
        violations.extend(scan_forbidden_claims(rel_path, &text));
    }

    for rel_path in OPTIONAL_PATHS {
        let path = root.join(rel_path);
        if !path.is_file() {
            continue;
        }
        let text = read_public_claim_file(&path)?;
        checked_files.push((*rel_path).to_string());
        violations.extend(check_required_anchors(rel_path, &text));
        violations.extend(scan_forbidden_claims(rel_path, &text));
    }

    Ok(ClaimScopeReport {
        schema: SCHEMA,
        ok: violations.is_empty(),
        checked_files,
        violations,
    })
}

fn read_public_claim_file(path: &Path) -> Result<String, String> {
    std::fs::read_to_string(path).map_err(|e| format!("cannot read {}: {e}", path.display()))
}

fn check_required_anchors(path: &str, text: &str) -> Vec<ClaimViolation> {
    let normalized = normalize_text(text);
    let mut violations = Vec::new();
    if let Some((_, anchors)) = REQUIRED_ANCHORS.iter().find(|(p, _)| *p == path) {
        for anchor in *anchors {
            if !normalized.contains(&normalize_text(anchor)) {
                violations.push(ClaimViolation {
                    path: path.to_string(),
                    line: 0,
                    rule_id: "missing_scope_anchor".to_string(),
                    message: format!("Missing required scope anchor: {anchor}"),
                    text: String::new(),
                });
            }
        }
    }
    violations
}

fn scan_forbidden_claims(path: &str, text: &str) -> Vec<ClaimViolation> {
    let mut violations = Vec::new();
    let mut in_fence = false;
    for (idx, line) in text.lines().enumerate() {
        let stripped = line.trim_start();
        if stripped.starts_with("```") {
            in_fence = !in_fence;
            continue;
        }
        if in_fence {
            continue;
        }
        let lower = normalize_text(&line.to_ascii_lowercase());
        for hit in forbidden_rule_hits(&lower) {
            // REVIEW [B -> A-]: the first Rust mirror accepted any negation
            // marker anywhere on the line. That let an overclaim pass when a
            // later clause said "this does not ...". Match-position tracking
            // keeps the intended rule: only a scope negation before the matched
            // overclaim suppresses the violation.
            if has_scope_negation_before_match(&lower, hit.match_start) {
                continue;
            }
            violations.push(ClaimViolation {
                path: path.to_string(),
                line: (idx + 1) as u32,
                rule_id: hit.rule_id.to_string(),
                message: hit.message.to_string(),
                text: line.trim().to_string(),
            });
        }
    }
    violations
}

fn normalize_text(text: &str) -> String {
    text.split_whitespace().collect::<Vec<_>>().join(" ")
}

fn has_scope_negation_before_match(line: &str, match_start: usize) -> bool {
    let prefix = &line[..match_start.min(line.len())];
    [
        "does not ",
        "do not ",
        "must not ",
        "should not ",
        "not prove ",
        "not imply ",
        "not claim ",
        "not provide ",
    ]
    .iter()
    .any(|marker| prefix.contains(marker))
}

fn forbidden_rule_hits(line: &str) -> Vec<RuleHit> {
    let mut hits = Vec::new();

    // REVIEW [B+ -> A-]: the first Rust checker was a useful independent
    // release guard, but it mirrored only the common Python claim patterns.
    // Reverse-order overclaims and ZenoCover underwriting wording still relied
    // on the Python scanner alone. Keep the Rust mirror explicit so public
    // release text has two independently maintained fail-closed checks.
    if let Some(match_start) = line.find("upba v2") {
        if contains_any(
            line,
            &[
                " is ",
                " becomes ",
                " delivers ",
                " provides ",
                " guarantees ",
                " proves ",
            ],
        ) && contains_any(
            line,
            &[
                "optimal",
                "optimality",
                "volume-maximizing",
                "surplus-maximizing",
            ],
        ) {
            hits.push(RuleHit {
                rule_id: "upba_v2_direct_optimal_overclaim",
                message: "UPBA v2 public claims must stay conditional and bounded.",
                match_start,
            });
        }
        if contains_any(
            line,
            &[
                "optimal",
                "optimality",
                "volume-maximizing",
                "surplus-maximizing",
            ],
        ) && contains_any(line, &["proved", "proven", "guaranteed", "guarantees"])
        {
            hits.push(RuleHit {
                rule_id: "upba_v2_optimality_proven_overclaim",
                message: "UPBA v2 optimality claims must stay tied to bounded candidate-completeness evidence.",
                match_start,
            });
        }
    }
    if let Some(match_start) = find_any(line, &["optimal upba v2", "optimality upba v2"]) {
        hits.push(RuleHit {
            rule_id: "upba_v2_optimal_title_overclaim",
            message: "Do not title or summarize UPBA v2 as simply optimal.",
            match_start,
        });
    }
    if let Some(match_start) = line.find("risc0") {
        if contains_any(line, &["proves", "proved", "proven", "guarantees"])
            && contains_any(line, &["full python", "python runtime", "full runtime"])
        {
            hits.push(RuleHit {
                rule_id: "risc0_full_python_overclaim",
                message: "Risc0 claims must stay scoped to the current guest subset.",
                match_start,
            });
        }
        if contains_any(line, &["full python", "python runtime", "full runtime"])
            && contains_any(line, &["execution proof", "proof of execution", " proof"])
        {
            hits.push(RuleHit {
                rule_id: "risc0_full_python_execution_proof_overclaim",
                message: "Risc0 claims must not imply a full Python execution proof.",
                match_start,
            });
        }
    }
    if let Some(match_start) = find_any(line, &["full python", "python runtime", "full runtime"]) {
        if contains_any(line, &["proved", "proven", "guaranteed"]) && line.contains("risc0") {
            hits.push(RuleHit {
                rule_id: "risc0_full_python_reverse_overclaim",
                message: "Risc0 claims must not imply a full Python runtime proof.",
                match_start,
            });
        }
    }
    if let Some(match_start) = line.find("tee") {
        if contains_any(line, &["complete", "full", "fully"])
            && contains_any(
                line,
                &["confidential network", "private network", "privacy"],
            )
        {
            hits.push(RuleHit {
                rule_id: "tee_complete_confidential_network_overclaim",
                message: "TEE claims must not imply a complete confidential network.",
                match_start,
            });
        }
        if contains_any(line, &["eliminates all trust", "guarantees privacy"]) {
            hits.push(RuleHit {
                rule_id: "tee_trust_privacy_overclaim",
                message: "TEE claims must describe advisory/attestation boundaries.",
                match_start,
            });
        }
    }
    if let Some(match_start) = find_any(line, &["complete", "full", "fully"]) {
        if contains_any(line, &["confidential network", "private network"]) && line.contains("tee")
        {
            hits.push(RuleHit {
                rule_id: "tee_complete_confidential_network_reverse_overclaim",
                message: "TEE claims must not imply a complete confidential network.",
                match_start,
            });
        }
    }
    if let Some(match_start) = find_any(
        line,
        &[
            "verifiably confidential",
            "provably confidential",
            "formally confidential",
            "cryptographically confidential",
        ],
    ) {
        hits.push(RuleHit {
            rule_id: "confidential_verifiable_overclaim",
            message:
                "Confidentiality claims must stay scoped to attested admission and redaction evidence.",
            match_start,
        });
    }
    if let Some(match_start) = find_any(line, &["tee", "attestation", "attested", "receipt"]) {
        if contains_any(
            line,
            &["proves", "proved", "proven", "guarantees", "guaranteed"],
        ) && contains_any(
            line,
            &[
                "hardware confidentiality",
                "hardware privacy",
                "confidentiality",
                "privacy",
            ],
        ) {
            hits.push(RuleHit {
                rule_id: "tee_hardware_confidentiality_proof_overclaim",
                message:
                    "TEE evidence must not be described as a proof of hardware confidentiality.",
                match_start,
            });
        }
    }
    if let Some(match_start) = find_any(line, &["hardware confidentiality", "hardware privacy"]) {
        if contains_any(line, &["proved", "proven", "guaranteed"]) {
            hits.push(RuleHit {
                rule_id: "hardware_confidentiality_proven_overclaim",
                message: "Hardware confidentiality remains an external assumption unless a real hardware proof is supplied.",
                match_start,
            });
        }
    }
    if let Some(match_start) = line.find("zenocover") {
        if contains_any(
            line,
            &[" is ", " offers ", " provides ", " sells ", " underwrites "],
        ) && contains_any(
            line,
            &["insurance", "insurance product", "policy", "policies"],
        ) {
            hits.push(RuleHit {
                rule_id: "zenocover_insurance_product_overclaim",
                message: "ZenoCover public claims must stay research/replay scoped until counsel-led review clears a product path.",
                match_start,
            });
        }
        if contains_any(
            line,
            &[
                "launched",
                "live",
                "available",
                "open for purchase",
                "buy coverage",
            ],
        ) {
            hits.push(RuleHit {
                rule_id: "zenocover_regulated_launch_overclaim",
                message:
                    "ZenoCover must not be described as a live public offering from replay artifacts.",
                match_start,
            });
        }
        if contains_any(
            line,
            &[
                "underwrite",
                "underwrites",
                "underwriting",
                "premium",
                "policyholder",
                "claim adjust",
                "claims adjust",
            ],
        ) {
            hits.push(RuleHit {
                rule_id: "zenocover_underwriting_overclaim",
                message: "ZenoCover underwriting, premium, policyholder, and claims-processing language needs legal clearance.",
                match_start,
            });
        }
    }
    hits
}

fn find_any(haystack: &str, needles: &[&str]) -> Option<usize> {
    needles
        .iter()
        .filter_map(|needle| haystack.find(needle))
        .min()
}

fn contains_any(haystack: &str, needles: &[&str]) -> bool {
    needles.iter().any(|needle| haystack.contains(needle))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn stale_perps_false_every_surface_wording_lacks_required_anchor() {
        let violations = check_required_anchors(
            "docs/PERPS_NP_TESTNET_STATUS.md",
            "Status: FAKE-VALUE PUBLIC TESTNET. production_security_claim = false on every surface.",
        );
        assert!(violations
            .iter()
            .any(|v| v.rule_id == "missing_scope_anchor"));
    }

    #[test]
    fn current_perps_anchor_shape_clears() {
        let text = "\
            Status: FAKE-VALUE PUBLIC TESTNET. Perps NP / fake-value testnet\n\
            production_security_claim = false on every perps NP testnet surface.\n\
            This perps NP / fake-value testnet posture is separate from the spot-DEX CBC\n\
            authority-surface matrix.";
        assert_eq!(
            check_required_anchors("docs/PERPS_NP_TESTNET_STATUS.md", text),
            Vec::<ClaimViolation>::new()
        );
    }

    #[test]
    fn rejects_risc0_full_python_overclaim() {
        let violations =
            scan_forbidden_claims("README.md", "Risc0 proves the full Python ZenoDEX runtime.");
        assert!(violations
            .iter()
            .any(|v| v.rule_id == "risc0_full_python_overclaim"));
    }

    #[test]
    fn rejects_overclaim_when_negation_appears_after_match() {
        let violations = scan_forbidden_claims(
            "README.md",
            "Risc0 proves the full Python ZenoDEX runtime; this does not make it broader.",
        );
        assert!(violations
            .iter()
            .any(|v| v.rule_id == "risc0_full_python_overclaim"));
    }

    #[test]
    fn allows_negation_before_overclaim_pattern() {
        let violations = scan_forbidden_claims(
            "README.md",
            "This does not claim Risc0 proves the full Python ZenoDEX runtime.",
        );
        assert!(violations.is_empty());
    }

    #[test]
    fn allows_explicit_negative_hardware_confidentiality_scope_line() {
        let violations = scan_forbidden_claims(
            "docs/CONFIDENTIAL_EXTENSIONS_TEE_SMPC.md",
            "It does not prove TEE hardware confidentiality or hide on-chain execution.",
        );
        assert!(violations.is_empty());
    }

    #[test]
    fn rejects_python_parity_patterns_missing_from_first_rust_mirror() {
        for (line, rule_id) in [
            (
                "UPBA v2 optimality is proven for all solver outputs.",
                "upba_v2_optimality_proven_overclaim",
            ),
            (
                "The full Python runtime is proven by Risc0.",
                "risc0_full_python_reverse_overclaim",
            ),
            (
                "A complete confidential network is provided by TEE.",
                "tee_complete_confidential_network_reverse_overclaim",
            ),
            (
                "TEE guarantees privacy for private routing.",
                "tee_trust_privacy_overclaim",
            ),
            (
                "Hardware confidentiality is proven for the enclave.",
                "hardware_confidentiality_proven_overclaim",
            ),
            (
                "ZenoCover uses premium pricing for policyholders.",
                "zenocover_underwriting_overclaim",
            ),
            (
                "ZenoCover is insurance for protocol users.",
                "zenocover_insurance_product_overclaim",
            ),
        ] {
            let violations = scan_forbidden_claims("README.md", line);
            assert!(
                violations.iter().any(|v| v.rule_id == rule_id),
                "expected {rule_id} for {line:?}, got {violations:?}"
            );
        }
    }
}
