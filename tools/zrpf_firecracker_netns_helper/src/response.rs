use sha2::{Digest, Sha256};

use crate::{DecodedNetnsRequestV1, NetnsHelperErrorV1, NetnsOperationV1, PROTOCOL_VERSION_V1};

pub const RESPONSE_BYTES_V1: usize = 256;
pub const RESPONSE_MAGIC_V1: [u8; 16] = *b"ZRPFLNXNSRESV1!!";

const RESPONSE_DIGEST_OFFSET_V1: usize = 224;
const RESPONSE_STATUS_ACCEPTED_V1: u16 = 1;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct NetnsKernelObservationV1 {
    device: u64,
    inode: u64,
    process_count: u32,
    non_loopback_address_count: u32,
    non_loopback_route_count: u32,
    path_absent: bool,
    mount_present: bool,
}

impl NetnsKernelObservationV1 {
    pub fn for_operation(operation: NetnsOperationV1, device: u64, inode: u64) -> Self {
        let mount_present = matches!(
            operation,
            NetnsOperationV1::Create | NetnsOperationV1::Inspect
        );
        Self {
            device,
            inode,
            process_count: 0,
            non_loopback_address_count: 0,
            non_loopback_route_count: 0,
            path_absent: !mount_present,
            mount_present,
        }
    }
}

pub trait NetnsKernelV1 {
    fn execute(
        &mut self,
        request: &DecodedNetnsRequestV1,
    ) -> Result<NetnsKernelObservationV1, NetnsHelperErrorV1>;
}

pub fn execute_request_with_kernel_v1<K: NetnsKernelV1>(
    request_bytes: &[u8],
    kernel: &mut K,
) -> Result<[u8; RESPONSE_BYTES_V1], NetnsHelperErrorV1> {
    let request = crate::decode_request_v1(request_bytes)?;
    let observation = kernel.execute(&request)?;
    validate_observation(&request, &observation)?;
    Ok(encode_response_v1(&request, &observation))
}

fn validate_observation(
    request: &DecodedNetnsRequestV1,
    observation: &NetnsKernelObservationV1,
) -> Result<(), NetnsHelperErrorV1> {
    if observation.process_count != 0 {
        return Err(NetnsHelperErrorV1::ProcessMembershipNotEmpty);
    }
    if observation.non_loopback_address_count != 0 {
        return Err(NetnsHelperErrorV1::NonLoopbackAddressPresent);
    }
    if observation.non_loopback_route_count != 0 {
        return Err(NetnsHelperErrorV1::NonLoopbackRoutePresent);
    }
    let should_be_present = matches!(
        request.operation(),
        NetnsOperationV1::Create | NetnsOperationV1::Inspect
    );
    if observation.mount_present != should_be_present
        || observation.path_absent == should_be_present
        || observation.mount_present == observation.path_absent
    {
        return Err(NetnsHelperErrorV1::ResponseInvariant);
    }
    if should_be_present && (observation.device == 0 || observation.inode == 0) {
        return Err(NetnsHelperErrorV1::ResponseInvariant);
    }
    if matches!(
        request.operation(),
        NetnsOperationV1::Inspect | NetnsOperationV1::Destroy | NetnsOperationV1::Absence
    ) && (observation.device != request.expected_device()
        || observation.inode != request.expected_inode())
    {
        return Err(NetnsHelperErrorV1::NamespaceIdentityMismatch);
    }
    Ok(())
}

fn encode_response_v1(
    request: &DecodedNetnsRequestV1,
    observation: &NetnsKernelObservationV1,
) -> [u8; RESPONSE_BYTES_V1] {
    let mut response = [0_u8; RESPONSE_BYTES_V1];
    response[0..16].copy_from_slice(&RESPONSE_MAGIC_V1);
    response[16..18].copy_from_slice(&PROTOCOL_VERSION_V1.to_be_bytes());
    response[18..20].copy_from_slice(&request.operation().code().to_be_bytes());
    response[20..22].copy_from_slice(&RESPONSE_STATUS_ACCEPTED_V1.to_be_bytes());
    response[32..40].copy_from_slice(&observation.device.to_be_bytes());
    response[40..48].copy_from_slice(&observation.inode.to_be_bytes());
    response[48..52].copy_from_slice(&observation.process_count.to_be_bytes());
    response[52..56].copy_from_slice(&observation.non_loopback_address_count.to_be_bytes());
    response[56..60].copy_from_slice(&observation.non_loopback_route_count.to_be_bytes());
    response[60] = u8::from(observation.path_absent);
    response[61] = u8::from(observation.mount_present);
    response[64..96].copy_from_slice(&request.request_sha256());
    response[96..128].copy_from_slice(&sha256(request.namespace_root().as_bytes()));
    response[128..160].copy_from_slice(&sha256(request.namespace_name().as_bytes()));
    let digest = sha256(&response[..RESPONSE_DIGEST_OFFSET_V1]);
    response[RESPONSE_DIGEST_OFFSET_V1..].copy_from_slice(&digest);
    response
}

fn sha256(bytes: &[u8]) -> [u8; 32] {
    Sha256::digest(bytes).into()
}
