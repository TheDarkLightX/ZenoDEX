use sha2::{Digest, Sha256};
use zenodex_zrpf_firecracker_netns_helper_v1::{
    decode_request_v1, encode_request_v1, execute_request_with_kernel_v1, NetnsHelperErrorV1,
    NetnsKernelObservationV1, NetnsKernelV1, NetnsOperationV1, NetnsRequestInputV1,
    REQUEST_BYTES_V1, REQUEST_DIGEST_OFFSET_V1, REQUEST_FLAGS_OFFSET_V1,
    REQUEST_NAME_LENGTH_OFFSET_V1, REQUEST_NAME_OFFSET_V1, REQUEST_RESERVED_OFFSET_V1,
    REQUEST_ROOT_LENGTH_OFFSET_V1, REQUEST_ROOT_OFFSET_V1, REQUEST_TRUSTED_UID_OFFSET_V1,
};

const ROOT: &str = "/run/zenodex-netns-A7";
const NAME: &str = "run3b941x";
const DEVICE: u64 = 0x0102_0304_0506_0708;
const INODE: u64 = 0x1112_1314_1516_1718;

fn request(operation: NetnsOperationV1) -> Vec<u8> {
    let (expected_device, expected_inode) = match operation {
        NetnsOperationV1::Inspect | NetnsOperationV1::Destroy => (DEVICE, INODE),
        NetnsOperationV1::Create | NetnsOperationV1::Cleanup | NetnsOperationV1::Absence => (0, 0),
    };
    encode_request_v1(NetnsRequestInputV1 {
        operation,
        namespace_root: ROOT,
        namespace_name: NAME,
        expected_device,
        expected_inode,
    })
    .unwrap_or_else(|error| panic!("fixture rejected: {error}"))
}

fn rewrite_digest(bytes: &mut [u8]) {
    let digest: [u8; 32] = Sha256::digest(&bytes[..REQUEST_DIGEST_OFFSET_V1]).into();
    bytes[REQUEST_DIGEST_OFFSET_V1..].copy_from_slice(&digest);
}

#[derive(Default)]
struct ExactKernel {
    calls: Vec<NetnsOperationV1>,
}

impl NetnsKernelV1 for ExactKernel {
    fn execute(
        &mut self,
        request: &zenodex_zrpf_firecracker_netns_helper_v1::DecodedNetnsRequestV1,
    ) -> Result<NetnsKernelObservationV1, NetnsHelperErrorV1> {
        self.calls.push(request.operation());
        if request.operation() == NetnsOperationV1::Inspect
            && (request.expected_device() != DEVICE || request.expected_inode() != INODE)
        {
            return Err(NetnsHelperErrorV1::NamespaceIdentityMismatch);
        }
        Ok(NetnsKernelObservationV1::for_operation(
            request.operation(),
            if request.expected_device() == 0 {
                DEVICE
            } else {
                request.expected_device()
            },
            if request.expected_inode() == 0 {
                INODE
            } else {
                request.expected_inode()
            },
        ))
    }
}

#[test]
fn position_distinct_nonpalindromic_request_is_exact_and_routed_once() {
    let bytes = request(NetnsOperationV1::Inspect);
    assert_eq!(bytes.len(), REQUEST_BYTES_V1);
    let request_sha256 = Sha256::digest(&bytes);
    assert_eq!(
        format!("{request_sha256:x}"),
        "4eaca7fc26901d5232b991b27ac0d79e1209ed8e482971542d25af7566b4561e"
    );
    assert_eq!(
        &bytes[REQUEST_ROOT_OFFSET_V1..REQUEST_ROOT_OFFSET_V1 + ROOT.len()],
        ROOT.as_bytes()
    );
    assert_eq!(
        &bytes[REQUEST_NAME_OFFSET_V1..REQUEST_NAME_OFFSET_V1 + NAME.len()],
        NAME.as_bytes()
    );
    assert_ne!(ROOT.as_bytes(), NAME.as_bytes());

    let decoded = decode_request_v1(&bytes).expect("valid request must decode");
    assert_eq!(decoded.operation(), NetnsOperationV1::Inspect);
    assert_eq!(decoded.namespace_root(), ROOT);
    assert_eq!(decoded.namespace_name(), NAME);
    assert_eq!(decoded.expected_device(), DEVICE);
    assert_eq!(decoded.expected_inode(), INODE);

    let mut kernel = ExactKernel::default();
    let response =
        execute_request_with_kernel_v1(&bytes, &mut kernel).expect("exact request must execute");
    assert_eq!(response.len(), 256);
    assert_eq!(kernel.calls, vec![NetnsOperationV1::Inspect]);
}

#[test]
fn every_flag_and_reserved_bit_is_an_active_rejecting_witness() {
    let accepted = request(NetnsOperationV1::Inspect);
    for bit in 0..32 {
        let mut mutated = accepted.clone();
        let value = 1_u32 << bit;
        mutated[REQUEST_FLAGS_OFFSET_V1..REQUEST_FLAGS_OFFSET_V1 + 4]
            .copy_from_slice(&value.to_be_bytes());
        rewrite_digest(&mut mutated);
        assert_eq!(
            decode_request_v1(&mutated),
            Err(NetnsHelperErrorV1::RequestFlags),
            "flag bit {bit} was not distinguished"
        );
    }
    for bit in 0..32 {
        let mut mutated = accepted.clone();
        let value = 1_u32 << bit;
        mutated[REQUEST_TRUSTED_UID_OFFSET_V1..REQUEST_TRUSTED_UID_OFFSET_V1 + 4]
            .copy_from_slice(&value.to_be_bytes());
        rewrite_digest(&mut mutated);
        assert_eq!(
            decode_request_v1(&mutated),
            Err(NetnsHelperErrorV1::TrustedUid),
            "trusted UID bit {bit} was not distinguished"
        );
    }
    for byte_index in REQUEST_ROOT_OFFSET_V1 + ROOT.len()..REQUEST_NAME_OFFSET_V1 {
        for bit in 0..8 {
            let mut mutated = accepted.clone();
            mutated[byte_index] ^= 1 << bit;
            rewrite_digest(&mut mutated);
            assert_eq!(
                decode_request_v1(&mutated),
                Err(NetnsHelperErrorV1::NamespaceRootPadding),
                "root padding bit {bit} at byte {byte_index} was not distinguished"
            );
        }
    }
    for byte_index in REQUEST_NAME_OFFSET_V1 + NAME.len()..REQUEST_RESERVED_OFFSET_V1 {
        for bit in 0..8 {
            let mut mutated = accepted.clone();
            mutated[byte_index] ^= 1 << bit;
            rewrite_digest(&mut mutated);
            assert_eq!(
                decode_request_v1(&mutated),
                Err(NetnsHelperErrorV1::NamespaceNamePadding),
                "name padding bit {bit} at byte {byte_index} was not distinguished"
            );
        }
    }
    for byte_index in REQUEST_RESERVED_OFFSET_V1..REQUEST_DIGEST_OFFSET_V1 {
        for bit in 0..8 {
            let mut mutated = accepted.clone();
            mutated[byte_index] ^= 1 << bit;
            rewrite_digest(&mut mutated);
            assert_eq!(
                decode_request_v1(&mutated),
                Err(NetnsHelperErrorV1::RequestReserved),
                "reserved bit {bit} at byte {byte_index} was not distinguished"
            );
        }
    }
}

#[test]
fn every_fixed_tag_byte_and_operation_tag_has_an_active_witness() {
    let accepted = request(NetnsOperationV1::Inspect);
    for byte_index in 0..16 {
        let mut mutated = accepted.clone();
        mutated[byte_index] ^= 1;
        rewrite_digest(&mut mutated);
        assert_eq!(
            decode_request_v1(&mutated),
            Err(NetnsHelperErrorV1::RequestMagic),
            "magic byte {byte_index} was not distinguished"
        );
    }
    for byte_index in 16..18 {
        let mut mutated = accepted.clone();
        mutated[byte_index] ^= 1;
        rewrite_digest(&mut mutated);
        assert!(
            matches!(
                decode_request_v1(&mutated),
                Err(NetnsHelperErrorV1::RequestVersion(_))
            ),
            "version byte {byte_index} was not distinguished"
        );
    }
    for operation in [
        NetnsOperationV1::Create,
        NetnsOperationV1::Inspect,
        NetnsOperationV1::Destroy,
        NetnsOperationV1::Cleanup,
        NetnsOperationV1::Absence,
    ] {
        let decoded = decode_request_v1(&request(operation)).expect("operation must decode");
        assert_eq!(decoded.operation(), operation);
    }
    for invalid in [0_u16, 6, 0x0100, u16::MAX] {
        let mut mutated = accepted.clone();
        mutated[18..20].copy_from_slice(&invalid.to_be_bytes());
        rewrite_digest(&mut mutated);
        assert_eq!(
            decode_request_v1(&mutated),
            Err(NetnsHelperErrorV1::RequestOperation(invalid))
        );
    }
}

#[test]
fn every_identity_byte_and_payload_position_is_observable() {
    let accepted = request(NetnsOperationV1::Inspect);
    for byte_index in 32..48 {
        let mut mutated = accepted.clone();
        mutated[byte_index] ^= 1;
        rewrite_digest(&mut mutated);
        let decoded = decode_request_v1(&mutated).expect("identity mutation remains framed");
        assert_ne!(
            (decoded.expected_device(), decoded.expected_inode()),
            (DEVICE, INODE),
            "identity byte {byte_index} was not distinguished"
        );
        let mut kernel = ExactKernel::default();
        assert_eq!(
            execute_request_with_kernel_v1(&mutated, &mut kernel),
            Err(NetnsHelperErrorV1::NamespaceIdentityMismatch)
        );
    }

    for (slot_offset, length) in [
        (REQUEST_ROOT_OFFSET_V1, ROOT.len()),
        (REQUEST_NAME_OFFSET_V1, NAME.len()),
    ] {
        for relative in 0..length {
            let mut mutated = accepted.clone();
            let offset = slot_offset + relative;
            mutated[offset] = if mutated[offset] == b'x' { b'y' } else { b'x' };
            rewrite_digest(&mut mutated);
            match decode_request_v1(&mutated) {
                Ok(decoded) => {
                    assert!(
                        decoded.namespace_root() != ROOT || decoded.namespace_name() != NAME,
                        "payload byte {offset} was not distinguished"
                    );
                }
                Err(
                    NetnsHelperErrorV1::NamespaceRootCanonical
                    | NetnsHelperErrorV1::NamespaceNameCanonical,
                ) => {}
                result => panic!("unexpected payload witness result at {offset}: {result:?}"),
            }
        }
    }
}

#[test]
fn length_endian_digest_and_position_choices_are_distinguished() {
    let accepted = request(NetnsOperationV1::Inspect);

    assert_eq!(
        decode_request_v1(&accepted[..accepted.len() - 1]),
        Err(NetnsHelperErrorV1::RequestSize)
    );
    let mut extended = accepted.clone();
    extended.push(0);
    assert_eq!(
        decode_request_v1(&extended),
        Err(NetnsHelperErrorV1::RequestSize)
    );

    let mut root_length = accepted.clone();
    root_length[REQUEST_ROOT_LENGTH_OFFSET_V1..REQUEST_ROOT_LENGTH_OFFSET_V1 + 2]
        .copy_from_slice(&(ROOT.len() as u16 - 1).to_be_bytes());
    rewrite_digest(&mut root_length);
    assert_eq!(
        decode_request_v1(&root_length),
        Err(NetnsHelperErrorV1::NamespaceRootPadding)
    );

    let mut name_length = accepted.clone();
    name_length[REQUEST_NAME_LENGTH_OFFSET_V1..REQUEST_NAME_LENGTH_OFFSET_V1 + 2]
        .copy_from_slice(&(NAME.len() as u16 - 1).to_be_bytes());
    rewrite_digest(&mut name_length);
    assert_eq!(
        decode_request_v1(&name_length),
        Err(NetnsHelperErrorV1::NamespaceNamePadding)
    );

    let mut little_endian_uid = accepted.clone();
    little_endian_uid[REQUEST_TRUSTED_UID_OFFSET_V1..REQUEST_TRUSTED_UID_OFFSET_V1 + 4]
        .copy_from_slice(&1_u32.to_le_bytes());
    rewrite_digest(&mut little_endian_uid);
    assert_eq!(
        decode_request_v1(&little_endian_uid),
        Err(NetnsHelperErrorV1::TrustedUid)
    );

    let mut swapped_positions = accepted.clone();
    swapped_positions[REQUEST_ROOT_OFFSET_V1] = b'r';
    swapped_positions[REQUEST_NAME_OFFSET_V1] = b'/';
    rewrite_digest(&mut swapped_positions);
    assert!(matches!(
        decode_request_v1(&swapped_positions),
        Err(NetnsHelperErrorV1::NamespaceRootCanonical)
            | Err(NetnsHelperErrorV1::NamespaceNameCanonical)
    ));

    for index in REQUEST_DIGEST_OFFSET_V1..REQUEST_BYTES_V1 {
        let mut digest = accepted.clone();
        digest[index] ^= 1;
        assert_eq!(
            decode_request_v1(&digest),
            Err(NetnsHelperErrorV1::RequestDigest),
            "digest byte {index} was not distinguished"
        );
    }
}

#[test]
fn operation_specific_identity_and_big_endian_identity_are_enforced() {
    for operation in [NetnsOperationV1::Create, NetnsOperationV1::Cleanup] {
        let mut bytes = request(operation);
        bytes[32..40].copy_from_slice(&DEVICE.to_be_bytes());
        bytes[40..48].copy_from_slice(&INODE.to_be_bytes());
        rewrite_digest(&mut bytes);
        assert_eq!(
            decode_request_v1(&bytes),
            Err(NetnsHelperErrorV1::UnexpectedIdentity)
        );
    }

    let accepted = request(NetnsOperationV1::Inspect);
    let mut little_endian = accepted.clone();
    little_endian[32..40].copy_from_slice(&DEVICE.to_le_bytes());
    little_endian[40..48].copy_from_slice(&INODE.to_le_bytes());
    rewrite_digest(&mut little_endian);
    let mut kernel = ExactKernel::default();
    assert_eq!(
        execute_request_with_kernel_v1(&little_endian, &mut kernel),
        Err(NetnsHelperErrorV1::NamespaceIdentityMismatch)
    );

    struct WrongAbsenceIdentity;
    impl NetnsKernelV1 for WrongAbsenceIdentity {
        fn execute(
            &mut self,
            request: &zenodex_zrpf_firecracker_netns_helper_v1::DecodedNetnsRequestV1,
        ) -> Result<NetnsKernelObservationV1, NetnsHelperErrorV1> {
            Ok(NetnsKernelObservationV1::for_operation(
                request.operation(),
                DEVICE,
                INODE,
            ))
        }
    }
    assert_eq!(
        execute_request_with_kernel_v1(
            &request(NetnsOperationV1::Absence),
            &mut WrongAbsenceIdentity,
        ),
        Err(NetnsHelperErrorV1::NamespaceIdentityMismatch)
    );
}
