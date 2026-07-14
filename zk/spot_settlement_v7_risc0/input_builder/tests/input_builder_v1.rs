mod support;

use zenodex_zrpf_risc0_spot_settlement_v7_input_builder::{
    build_canonical_spot_settlement_v7_guest_input_v1, SpotSettlementV7InputBuilderErrorV1,
    SPOT_SETTLEMENT_V7_INPUT_BUILDER_PRODUCTION_AUTHORITY,
    SPOT_SETTLEMENT_V7_INPUT_BUILDER_RECEIPT_AUTHORITY,
    SPOT_SETTLEMENT_V7_INPUT_BUILDER_SETTLEMENT_AUTHORITY,
};
use zenodex_zrpf_risc0_spot_settlement_v7_shared::decode_exact_spot_settlement_v7_guest_envelope_v1;

use support::canonical_components;

const _: () = assert!(!SPOT_SETTLEMENT_V7_INPUT_BUILDER_RECEIPT_AUTHORITY);
const _: () = assert!(!SPOT_SETTLEMENT_V7_INPUT_BUILDER_SETTLEMENT_AUTHORITY);
const _: () = assert!(!SPOT_SETTLEMENT_V7_INPUT_BUILDER_PRODUCTION_AUTHORITY);

#[test]
fn malformed_source_journal_rejects_before_envelope_construction() {
    assert_eq!(
        build_canonical_spot_settlement_v7_guest_input_v1(
            b"not-a-v6-journal",
            b"not-a-da-certificate",
            b"not-a-v6-replay",
            b"not-a-v7-host-input",
        ),
        Err(SpotSettlementV7InputBuilderErrorV1::ComponentDecode(
            "source child journal",
        )),
    );
}

#[test]
fn canonical_components_build_one_exact_deterministic_v7_envelope() {
    let components = canonical_components();
    let first = build_canonical_spot_settlement_v7_guest_input_v1(
        &components.source_child_journal,
        &components.data_availability_certificate,
        &components.replay,
        &components.state_root_host_input,
    )
    .unwrap();
    let second = build_canonical_spot_settlement_v7_guest_input_v1(
        &components.source_child_journal,
        &components.data_availability_certificate,
        &components.replay,
        &components.state_root_host_input,
    )
    .unwrap();
    let envelope = decode_exact_spot_settlement_v7_guest_envelope_v1(&first).unwrap();

    assert_eq!(second, first);
    assert_eq!(
        envelope.source_child_journal_bytes(),
        components.source_child_journal
    );
    assert_eq!(
        envelope.proposed_data_availability_certificate_bytes(),
        components.data_availability_certificate
    );
    assert_eq!(envelope.proposed_replay_bytes(), components.replay);
    assert_eq!(
        envelope.proposed_state_root_host_input_bytes(),
        components.state_root_host_input
    );
}

#[test]
fn every_component_rejects_trailing_bytes_at_its_exact_decoder() {
    let components = canonical_components();
    let cases = [
        (0, components.source_child_journal),
        (1, components.data_availability_certificate),
        (2, components.replay),
        (3, components.state_root_host_input),
    ];

    for (index, mut changed) in cases {
        changed.push(0);
        let canonical = canonical_components();
        let mut inputs = [
            canonical.source_child_journal,
            canonical.data_availability_certificate,
            canonical.replay,
            canonical.state_root_host_input,
        ];
        inputs[index] = changed;
        assert_eq!(
            build_canonical_spot_settlement_v7_guest_input_v1(
                &inputs[0], &inputs[1], &inputs[2], &inputs[3]
            ),
            Err(SpotSettlementV7InputBuilderErrorV1::ComponentDecode(
                [
                    "source child journal",
                    "data availability certificate",
                    "source replay",
                    "state-root host input",
                ][index],
            )),
        );
    }
}
