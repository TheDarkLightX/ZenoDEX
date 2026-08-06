use serde::Serialize;
use sha2::{Digest, Sha256};
use zenodex_zrpf_protocol_v3::{
    decode_exact_global_economic_lane_registry_v1, encode_global_economic_lane_registry_v1,
    CommitmentV3, EconomicLaneCommandStatusV1, EconomicLaneIdV1, EconomicLaneRegistryEntryV1,
    GlobalEconomicLaneRegistryV1, GlobalSettlementAbiErrorV1, ECONOMIC_LANE_COUNT_V1,
    GLOBAL_ECONOMIC_LANE_REGISTRY_VERSION_V1, MAX_GLOBAL_ECONOMIC_LANE_REGISTRY_BYTES_V1,
};

const REGISTRY_COMMITMENT_DOMAIN_V1: &[u8] = b"zenodex.global_settlement.economic_lane_registry.v1";

fn commitment(index: usize) -> CommitmentV3 {
    let mut bytes = [0_u8; 32];
    bytes[24..].copy_from_slice(&(index as u64 + 1).to_be_bytes());
    CommitmentV3::new(bytes).unwrap()
}

fn canonical_entries(enabled: &[EconomicLaneIdV1]) -> Vec<EconomicLaneRegistryEntryV1> {
    EconomicLaneIdV1::ALL
        .iter()
        .copied()
        .enumerate()
        .map(|(index, lane_id)| {
            let command_status = if enabled.contains(&lane_id) {
                EconomicLaneCommandStatusV1::Enabled
            } else {
                EconomicLaneCommandStatusV1::Disabled
            };
            EconomicLaneRegistryEntryV1::new(lane_id, command_status, commitment(index))
        })
        .collect()
}

fn registry(enabled: &[EconomicLaneIdV1]) -> GlobalEconomicLaneRegistryV1 {
    GlobalEconomicLaneRegistryV1::new(canonical_entries(enabled)).unwrap()
}

fn prefixed_domain_hasher(domain: &[u8]) -> Sha256 {
    let mut hasher = Sha256::new();
    hasher.update(u16::try_from(domain.len()).unwrap().to_be_bytes());
    hasher.update(domain);
    hasher
}

fn manual_registry_commitment(registry: &GlobalEconomicLaneRegistryV1) -> [u8; 32] {
    let mut hasher = prefixed_domain_hasher(REGISTRY_COMMITMENT_DOMAIN_V1);
    hasher.update(registry.registry_version().to_be_bytes());
    hasher.update(
        u16::try_from(registry.entries().len())
            .unwrap()
            .to_be_bytes(),
    );
    for entry in registry.entries() {
        hasher.update([entry.lane_id().code()]);
        hasher.update([entry.command_status().code()]);
        hasher.update(entry.module_release_registry_root().as_bytes());
    }
    hasher.finalize().into()
}

fn hex_32(value: &str) -> [u8; 32] {
    assert_eq!(value.len(), 64);
    let mut bytes = [0_u8; 32];
    for (index, byte) in bytes.iter_mut().enumerate() {
        *byte = u8::from_str_radix(&value[index * 2..index * 2 + 2], 16).unwrap();
    }
    bytes
}

#[test]
fn exact_closed_lane_vocabulary_round_trips_with_unique_codes() {
    // Arrange
    let expected = [
        (EconomicLaneIdV1::AssetTransfer, "ASSET_TRANSFER"),
        (EconomicLaneIdV1::SpotLiquidity, "SPOT_LIQUIDITY"),
        (EconomicLaneIdV1::FarmIncentives, "FARM_INCENTIVES"),
        (EconomicLaneIdV1::ZdexTokenomics, "ZDEX_TOKENOMICS"),
        (EconomicLaneIdV1::ZusdMonetary, "ZUSD_MONETARY"),
        (EconomicLaneIdV1::PerpsMarket, "PERPS_MARKET"),
        (EconomicLaneIdV1::OracleMarket, "ORACLE_MARKET"),
        (EconomicLaneIdV1::SealedAuction, "SEALED_AUCTION"),
        (EconomicLaneIdV1::StrategyEscrow, "STRATEGY_ESCROW"),
        (EconomicLaneIdV1::ProofRewards, "PROOF_REWARDS"),
        (EconomicLaneIdV1::ExternalCustody, "EXTERNAL_CUSTODY"),
        (
            EconomicLaneIdV1::GovernanceMigration,
            "GOVERNANCE_MIGRATION",
        ),
    ];

    // Act and assert
    assert_eq!(EconomicLaneIdV1::ALL, expected.map(|(lane, _)| lane));
    assert_eq!(ECONOMIC_LANE_COUNT_V1, expected.len());
    for (index, (lane, label)) in expected.iter().copied().enumerate() {
        assert_eq!(lane.code(), u8::try_from(index).unwrap());
        assert_eq!(lane.as_str(), label);
        assert_eq!(EconomicLaneIdV1::parse_exact(label), Ok(lane));
        assert_eq!(EconomicLaneIdV1::from_code(lane.code()), Ok(lane));
    }
    for unknown_code in [u8::try_from(ECONOMIC_LANE_COUNT_V1).unwrap(), u8::MAX] {
        assert_eq!(
            EconomicLaneIdV1::from_code(unknown_code),
            Err(GlobalSettlementAbiErrorV1::UnknownLaneCode(unknown_code))
        );
    }
}

#[test]
fn identifier_boundary_and_one_defect_mutants_reject_without_registry_change() {
    // Arrange
    let registry = registry(&[EconomicLaneIdV1::AssetTransfer]);
    let before = registry.clone();
    let before_commitment = registry.canonical_commitment().unwrap();
    let mutants = [
        "",
        "ASSET_TRANSFE",
        "ASSET_TRANSFERX",
        "aSSET_TRANSFER",
        "ASSET_TRANSFER ",
        " ASSET_TRANSFER",
        "ASSET_TRANSFER\0",
        "UNKNOWN_LANE",
    ];

    // Act and assert
    for mutant in mutants {
        assert_eq!(
            registry.resolve_new_command_lane(mutant),
            Err(GlobalSettlementAbiErrorV1::UnknownLaneIdentifier)
        );
        assert_eq!(registry, before);
        assert_eq!(registry.canonical_commitment().unwrap(), before_commitment);
    }
}

#[test]
fn every_known_identifier_rejects_a_single_case_mutation() {
    // Arrange
    let registry = registry(&EconomicLaneIdV1::ALL);

    // Act and assert
    for lane_id in EconomicLaneIdV1::ALL {
        let mut bytes = lane_id.as_str().as_bytes().to_vec();
        bytes[0] = bytes[0].to_ascii_lowercase();
        let mutant = core::str::from_utf8(&bytes).unwrap();
        assert_eq!(
            registry.resolve_new_command_lane(mutant),
            Err(GlobalSettlementAbiErrorV1::UnknownLaneIdentifier)
        );
    }
}

#[test]
fn disabled_lane_rejects_and_enabled_lane_admits_without_mutation() {
    // Arrange
    let registry = registry(&[EconomicLaneIdV1::SpotLiquidity]);
    let before = registry.clone();

    // Act
    let disabled = registry.resolve_new_command_lane("ASSET_TRANSFER");
    let enabled = registry.resolve_new_command_lane("SPOT_LIQUIDITY");

    // Assert
    assert_eq!(
        disabled,
        Err(GlobalSettlementAbiErrorV1::LaneDisabled(
            EconomicLaneIdV1::AssetTransfer
        ))
    );
    assert_eq!(enabled, Ok(EconomicLaneIdV1::SpotLiquidity));
    assert_eq!(registry, before);
}

#[test]
fn registry_cardinality_boundaries_and_canonical_order_fail_closed() {
    // Arrange
    let canonical = canonical_entries(&[]);

    // Act and assert
    for actual in [0_usize, 1, ECONOMIC_LANE_COUNT_V1 - 1] {
        assert_eq!(
            GlobalEconomicLaneRegistryV1::new(canonical[..actual].to_vec()),
            Err(GlobalSettlementAbiErrorV1::WrongLaneCount {
                actual,
                expected: ECONOMIC_LANE_COUNT_V1,
            })
        );
    }
    assert!(GlobalEconomicLaneRegistryV1::new(canonical.clone()).is_ok());

    let mut excess = canonical.clone();
    excess.push(canonical[0]);
    assert_eq!(
        GlobalEconomicLaneRegistryV1::new(excess),
        Err(GlobalSettlementAbiErrorV1::WrongLaneCount {
            actual: ECONOMIC_LANE_COUNT_V1 + 1,
            expected: ECONOMIC_LANE_COUNT_V1,
        })
    );

    let mut duplicate = canonical.clone();
    duplicate[ECONOMIC_LANE_COUNT_V1 - 1] = canonical[0];
    assert_eq!(
        GlobalEconomicLaneRegistryV1::new(duplicate),
        Err(GlobalSettlementAbiErrorV1::DuplicateLane(
            EconomicLaneIdV1::AssetTransfer
        ))
    );

    let mut reordered = canonical;
    reordered.swap(0, 1);
    assert_eq!(
        GlobalEconomicLaneRegistryV1::new(reordered),
        Err(GlobalSettlementAbiErrorV1::NonCanonicalLaneOrder {
            position: 0,
            expected: EconomicLaneIdV1::AssetTransfer,
            actual: EconomicLaneIdV1::SpotLiquidity,
        })
    );
}

#[test]
fn registry_commitment_matches_independent_preimage_and_fixed_vector() {
    // Arrange
    let registry = registry(&[
        EconomicLaneIdV1::SpotLiquidity,
        EconomicLaneIdV1::OracleMarket,
    ]);

    // Act
    let actual = registry.canonical_commitment().unwrap().into_bytes();

    // Assert
    assert_eq!(actual, manual_registry_commitment(&registry));
    assert_eq!(
        actual,
        hex_32("d564854ac0ecbcbe63cf2f7a4ea459e2fd9568b7020ed06be352747090609fd2")
    );
}

#[derive(Serialize)]
struct RawRegistryV1 {
    registry_version: u16,
    entries: Vec<EconomicLaneRegistryEntryV1>,
}

#[test]
fn exact_codec_round_trips_and_rejects_version_trailing_and_size_boundaries() {
    // Arrange
    let registry = registry(&[EconomicLaneIdV1::GovernanceMigration]);
    let encoded = encode_global_economic_lane_registry_v1(&registry).unwrap();
    let encoded_sha256: [u8; 32] = Sha256::digest(&encoded).into();

    // Act and assert
    assert_eq!(
        encoded_sha256,
        hex_32("3fac997953febe4979b0257c128ec138a3d28b220a99db2305c46cad9e84fe66")
    );
    assert_eq!(
        decode_exact_global_economic_lane_registry_v1(&encoded),
        Ok(registry.clone())
    );
    assert_eq!(
        encode_global_economic_lane_registry_v1(
            &decode_exact_global_economic_lane_registry_v1(&encoded).unwrap()
        )
        .unwrap(),
        encoded
    );

    assert_eq!(
        decode_exact_global_economic_lane_registry_v1(&[]),
        Err(GlobalSettlementAbiErrorV1::EmptyInput)
    );
    assert_eq!(
        decode_exact_global_economic_lane_registry_v1(&vec![
            0_u8;
            MAX_GLOBAL_ECONOMIC_LANE_REGISTRY_BYTES_V1
                + 1
        ]),
        Err(GlobalSettlementAbiErrorV1::InputTooLarge {
            actual: MAX_GLOBAL_ECONOMIC_LANE_REGISTRY_BYTES_V1 + 1,
            maximum: MAX_GLOBAL_ECONOMIC_LANE_REGISTRY_BYTES_V1,
        })
    );

    let mut trailing = encoded.clone();
    trailing.push(0);
    assert_eq!(
        decode_exact_global_economic_lane_registry_v1(&trailing),
        Err(GlobalSettlementAbiErrorV1::TrailingBytes)
    );

    let mut unknown_lane_code = encoded.clone();
    unknown_lane_code[2] = u8::try_from(ECONOMIC_LANE_COUNT_V1).unwrap();
    assert_eq!(
        decode_exact_global_economic_lane_registry_v1(&unknown_lane_code),
        Err(GlobalSettlementAbiErrorV1::PostcardDecode)
    );

    let mut unknown_status_code = encoded.clone();
    unknown_status_code[3] = 2;
    assert_eq!(
        decode_exact_global_economic_lane_registry_v1(&unknown_status_code),
        Err(GlobalSettlementAbiErrorV1::PostcardDecode)
    );

    let wrong_version = postcard::to_allocvec(&RawRegistryV1 {
        registry_version: GLOBAL_ECONOMIC_LANE_REGISTRY_VERSION_V1 + 1,
        entries: registry.entries().to_vec(),
    })
    .unwrap();
    assert_eq!(
        decode_exact_global_economic_lane_registry_v1(&wrong_version),
        Err(GlobalSettlementAbiErrorV1::InvalidRegistryVersion(
            GLOBAL_ECONOMIC_LANE_REGISTRY_VERSION_V1 + 1
        ))
    );
}
