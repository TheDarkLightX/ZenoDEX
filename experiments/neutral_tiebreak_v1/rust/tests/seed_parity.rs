//! Cross-language parity for the seed source: the Rust `seed_commit` /
//! `seed_from_pairs` must reproduce the Python golden vectors byte-for-byte.

use neutral_tiebreak::{seed_commit, seed_from_pairs};

fn from_hex(s: &str) -> Vec<u8> {
    assert!(s.len() % 2 == 0, "odd-length hex: {s}");
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).expect("valid hex"))
        .collect()
}

#[test]
fn rust_matches_python_commit_vectors() {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/../commit_parity_vectors.tsv");
    let data = std::fs::read_to_string(path).expect("read commit_parity_vectors.tsv");
    let mut n = 0;
    for line in data.lines() {
        if line.trim().is_empty() {
            continue;
        }
        let p: Vec<&str> = line.split('\t').collect();
        assert_eq!(p.len(), 3, "expected value/nonce/commit: {line}");
        let got = seed_commit(&from_hex(p[0]), &from_hex(p[1])).to_vec();
        assert_eq!(got, from_hex(p[2]), "commit mismatch for line: {line}");
        n += 1;
    }
    assert!(n >= 4, "expected >=4 commit vectors, got {n}");
}

#[test]
fn rust_matches_python_seed_vectors() {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/../seed_parity_vectors.tsv");
    let data = std::fs::read_to_string(path).expect("read seed_parity_vectors.tsv");
    let mut n = 0;
    for line in data.lines() {
        if line.trim().is_empty() {
            continue;
        }
        let p: Vec<&str> = line.split('\t').collect();
        assert_eq!(p.len(), 2, "expected pairs/seed: {line}");
        let mut owned: Vec<(String, Vec<u8>)> = Vec::new();
        for tok in p[0].split(';') {
            let kv: Vec<&str> = tok.split(':').collect();
            assert_eq!(kv.len(), 2, "expected idhex:valhex: {tok}");
            let id = String::from_utf8(from_hex(kv[0])).expect("utf-8 id");
            owned.push((id, from_hex(kv[1])));
        }
        let pairs: Vec<(&str, &[u8])> =
            owned.iter().map(|(id, v)| (id.as_str(), v.as_slice())).collect();
        let got = seed_from_pairs(&pairs).to_vec();
        assert_eq!(got, from_hex(p[1]), "seed mismatch for line: {line}");
        n += 1;
    }
    assert!(n >= 3, "expected >=3 seed vectors, got {n}");
}
