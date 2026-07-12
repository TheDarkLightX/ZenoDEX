use std::{
    env, fs,
    path::{Path, PathBuf},
};

use risc0_zkvm::{compute_image_id, Digest as Risc0Digest};
use serde_json::{json, Value};
use sha2::{Digest as ShaDigest, Sha256};
use tau_state_proof_risc0_methods::{
    TAU_STATE_PROOF_RISC0_AGGREGATE_ELF, TAU_STATE_PROOF_RISC0_AGGREGATE_ID,
    TAU_STATE_PROOF_RISC0_GUEST_ELF, TAU_STATE_PROOF_RISC0_GUEST_ID,
    TAU_STATE_PROOF_RISC0_PERPS_NP_LEAF_ELF, TAU_STATE_PROOF_RISC0_PERPS_NP_LEAF_ID,
    TAU_STATE_PROOF_RISC0_SPOT_LEAF_ELF, TAU_STATE_PROOF_RISC0_SPOT_LEAF_ID,
    TAU_STATE_PROOF_RISC0_SUMMARY_LEAF_ELF, TAU_STATE_PROOF_RISC0_SUMMARY_LEAF_ID,
    TAU_STATE_PROOF_RISC0_ZUSD_LEAF_ELF, TAU_STATE_PROOF_RISC0_ZUSD_LEAF_ID,
};

const SDK_VERSION: &str = "3.0.5";

struct Method<'a> {
    name: &'static str,
    filename: &'static str,
    program: &'a [u8],
    generated_id: [u32; 8],
}

fn method_report(method: &Method<'_>, output_dir: &Path) -> Result<Value, String> {
    if method.program.is_empty() {
        return Err(format!("{} embedded program is empty", method.name));
    }
    if method.generated_id.iter().all(|word| *word == 0) {
        return Err(format!("{} generated image ID is all-zero", method.name));
    }
    let computed_id = compute_image_id(method.program)
        .map_err(|err| format!("{} image ID computation failed: {err}", method.name))?;
    let generated_id = Risc0Digest::from(method.generated_id);
    if computed_id != generated_id {
        return Err(format!(
            "{} generated image ID does not match embedded program",
            method.name
        ));
    }

    let artifact_path = output_dir.join(method.filename);
    let mut options = fs::OpenOptions::new();
    options.write(true).create_new(true);
    let mut artifact = options
        .open(&artifact_path)
        .map_err(|err| format!("create {}: {err}", method.filename))?;
    std::io::Write::write_all(&mut artifact, method.program)
        .map_err(|err| format!("write {}: {err}", method.filename))?;
    artifact
        .sync_all()
        .map_err(|err| format!("sync {}: {err}", method.filename))?;

    Ok(json!({
        "name": method.name,
        "artifact": method.filename,
        "program_format": "risc0_program_binary_v1compat_v3",
        "program_bytes": method.program.len(),
        "program_sha256": hex::encode(Sha256::digest(method.program)),
        "image_id": computed_id.to_string(),
        "generated_image_id_words": method.generated_id,
    }))
}

fn run() -> Result<Value, String> {
    let args: Vec<String> = env::args().collect();
    let [_, flag, output_dir] = args.as_slice() else {
        return Err("usage: recursive_artifact_export --output-dir <new-directory>".to_string());
    };
    if flag != "--output-dir" {
        return Err("usage: recursive_artifact_export --output-dir <new-directory>".to_string());
    }
    let output_dir = PathBuf::from(output_dir);
    fs::create_dir(&output_dir).map_err(|err| format!("create output directory: {err}"))?;

    let methods = [
        Method {
            name: "aggregate",
            filename: "aggregate.bin",
            program: TAU_STATE_PROOF_RISC0_AGGREGATE_ELF,
            generated_id: TAU_STATE_PROOF_RISC0_AGGREGATE_ID,
        },
        Method {
            name: "guest",
            filename: "guest.bin",
            program: TAU_STATE_PROOF_RISC0_GUEST_ELF,
            generated_id: TAU_STATE_PROOF_RISC0_GUEST_ID,
        },
        Method {
            name: "perps_np_leaf",
            filename: "perps_np_leaf.bin",
            program: TAU_STATE_PROOF_RISC0_PERPS_NP_LEAF_ELF,
            generated_id: TAU_STATE_PROOF_RISC0_PERPS_NP_LEAF_ID,
        },
        Method {
            name: "spot_leaf",
            filename: "spot_leaf.bin",
            program: TAU_STATE_PROOF_RISC0_SPOT_LEAF_ELF,
            generated_id: TAU_STATE_PROOF_RISC0_SPOT_LEAF_ID,
        },
        Method {
            name: "summary_leaf",
            filename: "summary_leaf.bin",
            program: TAU_STATE_PROOF_RISC0_SUMMARY_LEAF_ELF,
            generated_id: TAU_STATE_PROOF_RISC0_SUMMARY_LEAF_ID,
        },
        Method {
            name: "zusd_leaf",
            filename: "zusd_leaf.bin",
            program: TAU_STATE_PROOF_RISC0_ZUSD_LEAF_ELF,
            generated_id: TAU_STATE_PROOF_RISC0_ZUSD_LEAF_ID,
        },
    ];

    let reports = methods
        .iter()
        .map(|method| method_report(method, &output_dir))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(json!({
        "schema": "zenodex/risc0_recursive_embedded_artifacts/v1",
        "sdk_version": SDK_VERSION,
        "method_count": reports.len(),
        "methods": reports,
    }))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_embedded_program_rejects_before_artifact_write() {
        let output_dir = env::temp_dir().join(format!(
            "zenodex-recursive-artifact-export-test-{}",
            std::process::id()
        ));
        let _ = fs::remove_dir_all(&output_dir);
        fs::create_dir(&output_dir).unwrap();
        let method = Method {
            name: "empty",
            filename: "empty.bin",
            program: &[],
            generated_id: [1; 8],
        };

        assert_eq!(
            method_report(&method, &output_dir).unwrap_err(),
            "empty embedded program is empty"
        );
        assert!(!output_dir.join("empty.bin").exists());
        fs::remove_dir(output_dir).unwrap();
    }
}

fn main() {
    match run() {
        Ok(report) => println!(
            "{}",
            serde_json::to_string(&report).expect("artifact report serializes")
        ),
        Err(err) => {
            eprintln!("{err}");
            std::process::exit(2);
        }
    }
}
