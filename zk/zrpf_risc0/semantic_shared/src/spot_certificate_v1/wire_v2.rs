use zenodex_zrpf_protocol_v3::{
    AuthorizationGrantIdV1, AuthorizationScopeIdV1, AuthorizationSubjectIdV1,
};

use crate::SpotSettlementAuthorizationInputV1;

pub(crate) const AUTHORIZATION_BYTES_V2: usize = 32 + 32 + 8 + 32;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ExactWireErrorV2 {
    Truncated(&'static str),
    InvalidAuthorization(&'static str),
    ArithmeticOverflow(&'static str),
}

pub(crate) fn write_authorization_v2(
    bytes: &mut alloc::vec::Vec<u8>,
    authorization: SpotSettlementAuthorizationInputV1,
) -> Result<(), ExactWireErrorV2> {
    validate_authorization_v2(authorization)?;
    bytes.extend_from_slice(authorization.authorization_subject_id.as_bytes());
    bytes.extend_from_slice(authorization.authorization_scope_id.as_bytes());
    bytes.extend_from_slice(&authorization.authorization_nonce.to_be_bytes());
    bytes.extend_from_slice(authorization.authorization_grant_id.as_bytes());
    Ok(())
}

pub(crate) fn read_authorization_v2(
    cursor: &mut ExactCursorV2<'_>,
) -> Result<SpotSettlementAuthorizationInputV1, ExactWireErrorV2> {
    let authorization_subject_id = cursor.read_array("authorization_subject_id")?;
    let authorization_scope_id = cursor.read_array("authorization_scope_id")?;
    let authorization_nonce = cursor.read_u64("authorization_nonce")?;
    let authorization_grant_id = cursor.read_array("authorization_grant_id")?;
    checked_authorization_v2(
        authorization_subject_id,
        authorization_scope_id,
        authorization_nonce,
        authorization_grant_id,
    )
}

pub(crate) fn validate_authorization_v2(
    authorization: SpotSettlementAuthorizationInputV1,
) -> Result<(), ExactWireErrorV2> {
    checked_authorization_v2(
        authorization.authorization_subject_id.into_bytes(),
        authorization.authorization_scope_id.into_bytes(),
        authorization.authorization_nonce,
        authorization.authorization_grant_id.into_bytes(),
    )?;
    Ok(())
}

fn checked_authorization_v2(
    authorization_subject_id: [u8; 32],
    authorization_scope_id: [u8; 32],
    authorization_nonce: u64,
    authorization_grant_id: [u8; 32],
) -> Result<SpotSettlementAuthorizationInputV1, ExactWireErrorV2> {
    let authorization_subject_id = AuthorizationSubjectIdV1::new(authorization_subject_id)
        .map_err(|_| ExactWireErrorV2::InvalidAuthorization("authorization_subject_id"))?;
    let authorization_scope_id = AuthorizationScopeIdV1::new(authorization_scope_id)
        .map_err(|_| ExactWireErrorV2::InvalidAuthorization("authorization_scope_id"))?;
    let authorization_grant_id = AuthorizationGrantIdV1::new(authorization_grant_id)
        .map_err(|_| ExactWireErrorV2::InvalidAuthorization("authorization_grant_id"))?;
    Ok(SpotSettlementAuthorizationInputV1 {
        authorization_subject_id,
        authorization_scope_id,
        authorization_nonce,
        authorization_grant_id,
    })
}

pub(crate) struct ExactCursorV2<'a> {
    bytes: &'a [u8],
    offset: usize,
}

impl<'a> ExactCursorV2<'a> {
    pub(crate) const fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, offset: 0 }
    }

    pub(crate) fn read_u16(&mut self, field: &'static str) -> Result<u16, ExactWireErrorV2> {
        Ok(u16::from_be_bytes(self.read_array(field)?))
    }

    pub(crate) fn read_u32_length(
        &mut self,
        field: &'static str,
    ) -> Result<usize, ExactWireErrorV2> {
        usize::try_from(u32::from_be_bytes(self.read_array(field)?))
            .map_err(|_| ExactWireErrorV2::ArithmeticOverflow(field))
    }

    fn read_u64(&mut self, field: &'static str) -> Result<u64, ExactWireErrorV2> {
        Ok(u64::from_be_bytes(self.read_array(field)?))
    }

    pub(crate) fn read_array<const N: usize>(
        &mut self,
        field: &'static str,
    ) -> Result<[u8; N], ExactWireErrorV2> {
        self.read_bytes(N, field)?
            .try_into()
            .map_err(|_| ExactWireErrorV2::Truncated(field))
    }

    pub(crate) fn read_bytes(
        &mut self,
        length: usize,
        field: &'static str,
    ) -> Result<&'a [u8], ExactWireErrorV2> {
        let end = self
            .offset
            .checked_add(length)
            .ok_or(ExactWireErrorV2::ArithmeticOverflow("cursor_offset"))?;
        let value = self
            .bytes
            .get(self.offset..end)
            .ok_or(ExactWireErrorV2::Truncated(field))?;
        self.offset = end;
        Ok(value)
    }

    pub(crate) const fn is_finished(&self) -> bool {
        self.offset == self.bytes.len()
    }
}

#[cfg(test)]
mod tests {
    use super::{checked_authorization_v2, ExactWireErrorV2};

    #[test]
    fn checked_authorization_rejects_each_zero_identifier() {
        for (subject, scope, grant, expected) in [
            (
                [0; 32],
                [2; 32],
                [3; 32],
                ExactWireErrorV2::InvalidAuthorization("authorization_subject_id"),
            ),
            (
                [1; 32],
                [0; 32],
                [3; 32],
                ExactWireErrorV2::InvalidAuthorization("authorization_scope_id"),
            ),
            (
                [1; 32],
                [2; 32],
                [0; 32],
                ExactWireErrorV2::InvalidAuthorization("authorization_grant_id"),
            ),
        ] {
            assert_eq!(
                checked_authorization_v2(subject, scope, 4, grant),
                Err(expected)
            );
        }
    }
}
