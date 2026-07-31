#![forbid(unsafe_code)]

use std::env;
use std::fs;

use zenodex_runtime_core::fcis_fee_apportionment::{
    apply_fee_apportionment_v2, canonical_evidence_sha256, encode_allocations_v2, encode_result_v2,
    encode_state_v2, AmountU256, AssetFeeAllocationV2, CommittedFeeApportionmentStateV2,
    FeeAmountCandidateV2, FeeApportionmentKeyV2, FeeDeficitEntryV2, FeeDistributionPolicyV2,
    SRGD_ALGORITHM_VERSION_V1,
};

fn hex_encode(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut output = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        output.push(HEX[usize::from(byte >> 4)] as char);
        output.push(HEX[usize::from(byte & 0x0f)] as char);
    }
    output
}

fn split_list(value: &str, delimiter: char, expected: usize) -> Result<Vec<&str>, String> {
    let parts: Vec<&str> = value.split(delimiter).collect();
    if parts.len() != expected || parts.iter().any(|part| part.is_empty()) {
        return Err(format!("expected {expected} nonempty list fields"));
    }
    Ok(parts)
}

fn parse_i32(value: &str, field: &str) -> Result<i32, String> {
    value
        .parse::<i32>()
        .map_err(|_| format!("{field} is not an i32"))
}

fn parse_u16(value: &str, field: &str) -> Result<u16, String> {
    value
        .parse::<u16>()
        .map_err(|_| format!("{field} is not a u16"))
}

fn join_u16(values: [u16; 3]) -> String {
    values
        .iter()
        .map(u16::to_string)
        .collect::<Vec<_>>()
        .join(",")
}

fn join_u8(values: [u8; 3]) -> String {
    values
        .iter()
        .map(u8::to_string)
        .collect::<Vec<_>>()
        .join(",")
}

fn join_i32(values: [i32; 3]) -> String {
    values
        .iter()
        .map(i32::to_string)
        .collect::<Vec<_>>()
        .join(",")
}

fn join_amounts(values: &[AmountU256; 3]) -> String {
    values
        .iter()
        .map(|value| value.as_biguint().to_str_radix(10))
        .collect::<Vec<_>>()
        .join(",")
}

fn join_allocation_u16(allocations: &[AssetFeeAllocationV2]) -> String {
    allocations
        .iter()
        .map(|allocation| join_u16(allocation.fractions()))
        .collect::<Vec<_>>()
        .join(";")
}

fn join_allocation_u8(allocations: &[AssetFeeAllocationV2]) -> String {
    allocations
        .iter()
        .map(|allocation| join_u8(allocation.bonuses()))
        .collect::<Vec<_>>()
        .join(";")
}

fn join_allocation_amounts(allocations: &[AssetFeeAllocationV2]) -> String {
    allocations
        .iter()
        .map(|allocation| join_amounts(allocation.amounts()))
        .collect::<Vec<_>>()
        .join(";")
}

fn join_allocation_i32(allocations: &[AssetFeeAllocationV2]) -> String {
    allocations
        .iter()
        .map(|allocation| join_i32(allocation.deficits_post()))
        .collect::<Vec<_>>()
        .join(";")
}

fn reject_line(id: &str, code: &str, path: &[String]) -> String {
    format!("{}|R|{}|{}", id, code, path.join("/"))
}

fn parse_record(line: &str) -> Result<String, String> {
    let fields: Vec<&str> = line.split('\t').collect();
    if fields.len() != 8 {
        return Err("expected eight tab-separated fields".to_owned());
    }
    let id = fields[0];
    let amount_values = split_list(fields[3], ',', fields[3].split(',').count())?;
    if amount_values.is_empty() {
        return Err("contribution amount list is empty".to_owned());
    }
    let domains = split_list(fields[1], ';', amount_values.len())?;
    let assets = split_list(fields[2], ';', amount_values.len())?;
    let weights = split_list(fields[4], ',', 3)?;
    let destinations = split_list(fields[5], ',', 3)?;
    let deficit_buyback = parse_i32(fields[6], "deficit_buyback")?;
    let deficit_treasury = parse_i32(fields[7], "deficit_treasury")?;

    let mut contributions = Vec::with_capacity(amount_values.len());
    let mut first_key = None;
    for (index, amount_text) in amount_values.iter().enumerate() {
        let key =
            FeeApportionmentKeyV2::try_new(domains[index].to_owned(), assets[index].to_owned())
                .map_err(|error| reject_line(id, error.code().as_str(), error.path()))?;
        if first_key.is_none() {
            first_key = Some(key.clone());
        }
        let amount = AmountU256::try_from_decimal(amount_text)
            .map_err(|error| reject_line(id, error.code().as_str(), error.path()))?;
        contributions.push(FeeAmountCandidateV2::new(key, amount));
    }
    let policy = FeeDistributionPolicyV2::try_new(
        [
            parse_u16(weights[0], "buyback weight")?,
            parse_u16(weights[1], "treasury weight")?,
            parse_u16(weights[2], "rewards weight")?,
        ],
        [
            destinations[0].to_owned(),
            destinations[1].to_owned(),
            destinations[2].to_owned(),
        ],
    )
    .map_err(|error| reject_line(id, error.code().as_str(), error.path()))?;
    let state = if deficit_buyback == 0 && deficit_treasury == 0 {
        CommittedFeeApportionmentStateV2::empty()
    } else {
        let entry = FeeDeficitEntryV2::try_new(
            first_key.ok_or_else(|| "missing first candidate key".to_owned())?,
            deficit_buyback,
            deficit_treasury,
        )
        .map_err(|error| reject_line(id, error.code().as_str(), error.path()))?;
        CommittedFeeApportionmentStateV2::try_new(SRGD_ALGORITHM_VERSION_V1.to_owned(), vec![entry])
            .map_err(|error| reject_line(id, error.code().as_str(), error.path()))?
    };

    let result = match apply_fee_apportionment_v2(&contributions, &policy, &state) {
        Ok(value) => value,
        Err(error) => return Ok(reject_line(id, error.code().as_str(), error.path())),
    };
    if result.allocations().is_empty() {
        return Err("accepted result has no allocation".to_owned());
    }
    let state_bytes = encode_state_v2(result.state());
    let allocation_bytes = encode_allocations_v2(result.allocations());
    let result_bytes = encode_result_v2(&result);
    let evidence_digest = canonical_evidence_sha256(&result_bytes);
    Ok(format!(
        "{}|A|{}|{}|{}|{}|{}|{}|{}|{}",
        id,
        join_allocation_u16(result.allocations()),
        join_allocation_u8(result.allocations()),
        join_allocation_amounts(result.allocations()),
        join_allocation_i32(result.allocations()),
        hex_encode(&state_bytes),
        hex_encode(&allocation_bytes),
        hex_encode(&result_bytes),
        evidence_digest,
    ))
}

fn main() {
    let arguments: Vec<String> = env::args().collect();
    if arguments.len() != 3 {
        eprintln!("usage: fcis-m6-b09-rust-parity INPUT.tsv OUTPUT.txt");
        std::process::exit(2);
    }
    let input = fs::read_to_string(&arguments[1]).unwrap_or_else(|error| {
        eprintln!("failed to read input: {error}");
        std::process::exit(2);
    });
    let mut output = String::new();
    for line in input.lines() {
        if line.is_empty() {
            continue;
        }
        let id = line.split('\t').next().unwrap_or("<malformed>");
        match parse_record(line) {
            Ok(record) => {
                output.push_str(&record);
                output.push('\n');
            }
            Err(error) if error.starts_with(id) && error.contains("|R|") => {
                output.push_str(&error);
                output.push('\n');
            }
            Err(error) => {
                eprintln!("record {id} failed outside the declared protocol: {error}");
                std::process::exit(1);
            }
        }
    }
    fs::write(&arguments[2], output).unwrap_or_else(|error| {
        eprintln!("failed to write output: {error}");
        std::process::exit(2);
    });
}
