use crate::SpotValueLeafInputErrorV4;

pub(crate) struct Cursor<'a> {
    bytes: &'a [u8],
    position: usize,
}

impl<'a> Cursor<'a> {
    pub(crate) const fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, position: 0 }
    }

    pub(crate) fn read_u8(&mut self) -> Result<u8, SpotValueLeafInputErrorV4> {
        let value = *self
            .bytes
            .get(self.position)
            .ok_or(SpotValueLeafInputErrorV4::Truncated)?;
        self.position = self
            .position
            .checked_add(1)
            .ok_or(SpotValueLeafInputErrorV4::LengthOverflow)?;
        Ok(value)
    }

    pub(crate) fn read_u16(&mut self) -> Result<u16, SpotValueLeafInputErrorV4> {
        Ok(u16::from_be_bytes(self.read_array()?))
    }

    pub(crate) fn read_u32(&mut self) -> Result<u32, SpotValueLeafInputErrorV4> {
        Ok(u32::from_be_bytes(self.read_array()?))
    }

    pub(crate) fn read_u128(&mut self) -> Result<u128, SpotValueLeafInputErrorV4> {
        Ok(u128::from_be_bytes(self.read_array()?))
    }

    pub(crate) fn read_array<const N: usize>(
        &mut self,
    ) -> Result<[u8; N], SpotValueLeafInputErrorV4> {
        self.read(N)?
            .try_into()
            .map_err(|_| SpotValueLeafInputErrorV4::Truncated)
    }

    pub(crate) fn read(&mut self, length: usize) -> Result<&'a [u8], SpotValueLeafInputErrorV4> {
        let end = self
            .position
            .checked_add(length)
            .ok_or(SpotValueLeafInputErrorV4::LengthOverflow)?;
        let value = self
            .bytes
            .get(self.position..end)
            .ok_or(SpotValueLeafInputErrorV4::Truncated)?;
        self.position = end;
        Ok(value)
    }

    pub(crate) fn finish(self) -> Result<(), SpotValueLeafInputErrorV4> {
        if self.position == self.bytes.len() {
            Ok(())
        } else {
            Err(SpotValueLeafInputErrorV4::TrailingBytes)
        }
    }
}
