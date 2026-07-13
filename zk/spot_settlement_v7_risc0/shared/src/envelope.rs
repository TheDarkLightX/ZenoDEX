use alloc::vec::Vec;

use zenodex_zrpf_protocol_v3::{
    MAX_FULL_BLOB_DA_CERTIFICATE_BYTES_V1, MAX_SETTLEMENT_ADMISSION_JOURNAL_BYTES_V1,
};
use zenodex_zrpf_risc0_spot_settlement_v6_shared::MAX_SOURCE_OPENED_SPOT_SETTLEMENT_REPLAY_BYTES_V3;
use zenodex_zrpf_risc0_spot_state_root_v7_semantic_shared::MAX_SPOT_STATE_ROOT_V7_HOST_INPUT_BYTES_V1;

use crate::SpotSettlementV7ErrorV1;

pub const SPOT_SETTLEMENT_V7_GUEST_ENVELOPE_VERSION_V1: u16 = 1;

const ENVELOPE_HEADER_BYTES_V1: usize = 2 + 4 * 4;

pub const MAX_SPOT_SETTLEMENT_V7_GUEST_ENVELOPE_BYTES_V1: usize = ENVELOPE_HEADER_BYTES_V1
    + MAX_SETTLEMENT_ADMISSION_JOURNAL_BYTES_V1
    + MAX_FULL_BLOB_DA_CERTIFICATE_BYTES_V1
    + MAX_SOURCE_OPENED_SPOT_SETTLEMENT_REPLAY_BYTES_V3
    + MAX_SPOT_STATE_ROOT_V7_HOST_INPUT_BYTES_V1;

/// Strictly framed, proof-neutral proposal for the V7 guest.
///
/// Only `source_child_journal_bytes` may be used before child receipt
/// verification, as the exact byte string passed to `env::verify`. All other
/// interpretation belongs after that call. Decoding grants no receipt or
/// settlement authority.
///
/// ```compile_fail
/// use zenodex_zrpf_risc0_spot_settlement_v7_shared::ProposedSpotSettlementV7EnvelopeV1;
/// let envelope: ProposedSpotSettlementV7EnvelopeV1 = unimplemented!();
/// let _ = envelope.receipt_verified();
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProposedSpotSettlementV7EnvelopeV1 {
    source_child_journal_bytes: Vec<u8>,
    data_availability_certificate_bytes: Vec<u8>,
    replay_bytes: Vec<u8>,
    state_root_host_input_bytes: Vec<u8>,
}

impl ProposedSpotSettlementV7EnvelopeV1 {
    pub fn new(
        source_child_journal_bytes: Vec<u8>,
        data_availability_certificate_bytes: Vec<u8>,
        replay_bytes: Vec<u8>,
        state_root_host_input_bytes: Vec<u8>,
    ) -> Result<Self, SpotSettlementV7ErrorV1> {
        require_component(
            "source child journal",
            source_child_journal_bytes.len(),
            MAX_SETTLEMENT_ADMISSION_JOURNAL_BYTES_V1,
        )?;
        require_component(
            "data availability certificate",
            data_availability_certificate_bytes.len(),
            MAX_FULL_BLOB_DA_CERTIFICATE_BYTES_V1,
        )?;
        require_component(
            "source replay",
            replay_bytes.len(),
            MAX_SOURCE_OPENED_SPOT_SETTLEMENT_REPLAY_BYTES_V3,
        )?;
        require_component(
            "state-root host input",
            state_root_host_input_bytes.len(),
            MAX_SPOT_STATE_ROOT_V7_HOST_INPUT_BYTES_V1,
        )?;
        encoded_length(
            source_child_journal_bytes.len(),
            data_availability_certificate_bytes.len(),
            replay_bytes.len(),
            state_root_host_input_bytes.len(),
        )?;
        Ok(Self {
            source_child_journal_bytes,
            data_availability_certificate_bytes,
            replay_bytes,
            state_root_host_input_bytes,
        })
    }

    pub fn source_child_journal_bytes(&self) -> &[u8] {
        &self.source_child_journal_bytes
    }

    pub fn proposed_data_availability_certificate_bytes(&self) -> &[u8] {
        &self.data_availability_certificate_bytes
    }

    pub fn proposed_replay_bytes(&self) -> &[u8] {
        &self.replay_bytes
    }

    pub fn proposed_state_root_host_input_bytes(&self) -> &[u8] {
        &self.state_root_host_input_bytes
    }
}

pub fn encode_spot_settlement_v7_guest_envelope_v1(
    envelope: &ProposedSpotSettlementV7EnvelopeV1,
) -> Result<Vec<u8>, SpotSettlementV7ErrorV1> {
    let total = encoded_length(
        envelope.source_child_journal_bytes.len(),
        envelope.data_availability_certificate_bytes.len(),
        envelope.replay_bytes.len(),
        envelope.state_root_host_input_bytes.len(),
    )?;
    let mut output = Vec::with_capacity(total);
    output.extend_from_slice(&SPOT_SETTLEMENT_V7_GUEST_ENVELOPE_VERSION_V1.to_be_bytes());
    write_component(
        &mut output,
        "source child journal",
        &envelope.source_child_journal_bytes,
    )?;
    write_component(
        &mut output,
        "data availability certificate",
        &envelope.data_availability_certificate_bytes,
    )?;
    write_component(&mut output, "source replay", &envelope.replay_bytes)?;
    write_component(
        &mut output,
        "state-root host input",
        &envelope.state_root_host_input_bytes,
    )?;
    Ok(output)
}

pub fn decode_exact_spot_settlement_v7_guest_envelope_v1(
    bytes: &[u8],
) -> Result<ProposedSpotSettlementV7EnvelopeV1, SpotSettlementV7ErrorV1> {
    if bytes.is_empty() {
        return Err(SpotSettlementV7ErrorV1::EmptyInput);
    }
    if bytes.len() > MAX_SPOT_SETTLEMENT_V7_GUEST_ENVELOPE_BYTES_V1 {
        return Err(SpotSettlementV7ErrorV1::InputTooLarge {
            actual: bytes.len(),
            maximum: MAX_SPOT_SETTLEMENT_V7_GUEST_ENVELOPE_BYTES_V1,
        });
    }
    let mut cursor = CursorV1::new(bytes);
    let version = cursor.read_u16("envelope version")?;
    if version != SPOT_SETTLEMENT_V7_GUEST_ENVELOPE_VERSION_V1 {
        return Err(SpotSettlementV7ErrorV1::InvalidEnvelopeVersion(version));
    }
    let source = cursor.read_component(
        "source child journal",
        MAX_SETTLEMENT_ADMISSION_JOURNAL_BYTES_V1,
    )?;
    let certificate = cursor.read_component(
        "data availability certificate",
        MAX_FULL_BLOB_DA_CERTIFICATE_BYTES_V1,
    )?;
    let replay = cursor.read_component(
        "source replay",
        MAX_SOURCE_OPENED_SPOT_SETTLEMENT_REPLAY_BYTES_V3,
    )?;
    let host = cursor.read_component(
        "state-root host input",
        MAX_SPOT_STATE_ROOT_V7_HOST_INPUT_BYTES_V1,
    )?;
    if !cursor.is_finished() {
        return Err(SpotSettlementV7ErrorV1::TrailingBytes);
    }
    let envelope = ProposedSpotSettlementV7EnvelopeV1::new(
        source.to_vec(),
        certificate.to_vec(),
        replay.to_vec(),
        host.to_vec(),
    )?;
    if encode_spot_settlement_v7_guest_envelope_v1(&envelope)?.as_slice() != bytes {
        return Err(SpotSettlementV7ErrorV1::NonCanonicalEnvelope);
    }
    Ok(envelope)
}

fn encoded_length(
    source: usize,
    certificate: usize,
    replay: usize,
    host: usize,
) -> Result<usize, SpotSettlementV7ErrorV1> {
    let total = ENVELOPE_HEADER_BYTES_V1
        .checked_add(source)
        .and_then(|value| value.checked_add(certificate))
        .and_then(|value| value.checked_add(replay))
        .and_then(|value| value.checked_add(host))
        .ok_or(SpotSettlementV7ErrorV1::LengthOverflow("envelope total"))?;
    if total > MAX_SPOT_SETTLEMENT_V7_GUEST_ENVELOPE_BYTES_V1 {
        return Err(SpotSettlementV7ErrorV1::InputTooLarge {
            actual: total,
            maximum: MAX_SPOT_SETTLEMENT_V7_GUEST_ENVELOPE_BYTES_V1,
        });
    }
    Ok(total)
}

fn require_component(
    component: &'static str,
    actual: usize,
    maximum: usize,
) -> Result<(), SpotSettlementV7ErrorV1> {
    if actual == 0 {
        return Err(SpotSettlementV7ErrorV1::EmptyComponent(component));
    }
    if actual > maximum {
        return Err(SpotSettlementV7ErrorV1::ComponentTooLarge {
            component,
            actual,
            maximum,
        });
    }
    Ok(())
}

fn write_component(
    output: &mut Vec<u8>,
    component: &'static str,
    bytes: &[u8],
) -> Result<(), SpotSettlementV7ErrorV1> {
    let length = u32::try_from(bytes.len())
        .map_err(|_| SpotSettlementV7ErrorV1::LengthOverflow(component))?;
    output.extend_from_slice(&length.to_be_bytes());
    output.extend_from_slice(bytes);
    Ok(())
}

struct CursorV1<'a> {
    bytes: &'a [u8],
    offset: usize,
}

impl<'a> CursorV1<'a> {
    const fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, offset: 0 }
    }

    fn read_u16(&mut self, field: &'static str) -> Result<u16, SpotSettlementV7ErrorV1> {
        Ok(u16::from_be_bytes(self.read_array(field)?))
    }

    fn read_u32(&mut self, field: &'static str) -> Result<u32, SpotSettlementV7ErrorV1> {
        Ok(u32::from_be_bytes(self.read_array(field)?))
    }

    fn read_component(
        &mut self,
        component: &'static str,
        maximum: usize,
    ) -> Result<&'a [u8], SpotSettlementV7ErrorV1> {
        let length = usize::try_from(self.read_u32(component)?)
            .map_err(|_| SpotSettlementV7ErrorV1::LengthOverflow(component))?;
        require_component(component, length, maximum)?;
        self.read(length, component)
    }

    fn read_array<const N: usize>(
        &mut self,
        field: &'static str,
    ) -> Result<[u8; N], SpotSettlementV7ErrorV1> {
        self.read(N, field)?
            .try_into()
            .map_err(|_| SpotSettlementV7ErrorV1::TruncatedInput(field))
    }

    fn read(
        &mut self,
        length: usize,
        field: &'static str,
    ) -> Result<&'a [u8], SpotSettlementV7ErrorV1> {
        let end = self
            .offset
            .checked_add(length)
            .ok_or(SpotSettlementV7ErrorV1::LengthOverflow(field))?;
        let value = self
            .bytes
            .get(self.offset..end)
            .ok_or(SpotSettlementV7ErrorV1::TruncatedInput(field))?;
        self.offset = end;
        Ok(value)
    }

    const fn is_finished(&self) -> bool {
        self.offset == self.bytes.len()
    }
}
