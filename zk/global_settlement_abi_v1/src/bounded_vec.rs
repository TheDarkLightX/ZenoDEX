use std::{fmt, marker::PhantomData};

use serde::de::{Error, IgnoredAny, SeqAccess, Visitor};
use serde::{Deserialize, Deserializer};

pub(crate) fn deserialize_bounded_vec_v1<'de, D, T, const MAXIMUM: usize>(
    deserializer: D,
    label: &'static str,
) -> Result<Vec<T>, D::Error>
where
    D: Deserializer<'de>,
    T: Deserialize<'de>,
{
    deserializer.deserialize_seq(BoundedVecVisitorV1::<T, MAXIMUM> {
        label,
        marker: PhantomData,
    })
}

struct BoundedVecVisitorV1<T, const MAXIMUM: usize> {
    label: &'static str,
    marker: PhantomData<T>,
}

impl<'de, T, const MAXIMUM: usize> Visitor<'de> for BoundedVecVisitorV1<T, MAXIMUM>
where
    T: Deserialize<'de>,
{
    type Value = Vec<T>;

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{} with at most {MAXIMUM} entries", self.label)
    }

    fn visit_seq<A>(self, mut sequence: A) -> Result<Self::Value, A::Error>
    where
        A: SeqAccess<'de>,
    {
        if sequence.size_hint().is_some_and(|size| size > MAXIMUM) {
            return Err(A::Error::custom(format_args!(
                "{} exceeds the V1 bound of {MAXIMUM} entries",
                self.label
            )));
        }

        let mut values = Vec::with_capacity(sequence.size_hint().unwrap_or(0).min(MAXIMUM));
        while values.len() < MAXIMUM {
            match sequence.next_element()? {
                Some(value) => values.push(value),
                None => return Ok(values),
            }
        }

        if sequence.next_element::<IgnoredAny>()?.is_some() {
            return Err(A::Error::custom(format_args!(
                "{} exceeds the V1 bound of {MAXIMUM} entries",
                self.label
            )));
        }
        Ok(values)
    }
}

#[cfg(test)]
mod tests {
    use std::{cell::Cell, rc::Rc};

    use serde::de::value::{Error as ValueError, SeqDeserializer};

    use super::deserialize_bounded_vec_v1;

    struct ExactSizeHostileIterator {
        next_calls: Rc<Cell<usize>>,
    }

    impl Iterator for ExactSizeHostileIterator {
        type Item = u8;

        fn next(&mut self) -> Option<Self::Item> {
            self.next_calls.set(self.next_calls.get() + 1);
            Some(0)
        }

        fn size_hint(&self) -> (usize, Option<usize>) {
            (3, Some(3))
        }
    }

    #[test]
    fn oversized_exact_size_sequence_rejects_before_first_element() {
        let next_calls = Rc::new(Cell::new(0));
        let sequence = SeqDeserializer::<_, ValueError>::new(ExactSizeHostileIterator {
            next_calls: Rc::clone(&next_calls),
        });

        let error = deserialize_bounded_vec_v1::<_, u8, 2>(sequence, "test rows").unwrap_err();

        assert!(error.to_string().contains("test rows exceeds the V1 bound"));
        assert_eq!(next_calls.get(), 0);
    }
}
