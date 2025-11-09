use core::{fmt, marker::PhantomData};

use serde_core::{
  de::{Error, SeqAccess, Visitor},
  Deserialize, Deserializer, Serialize, Serializer,
};

use super::{ArrayLength, GenericArrayDeque};

impl<T: Serialize, N: ArrayLength> Serialize for GenericArrayDeque<T, N> {
  fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
  where
    S: Serializer,
  {
    serializer.collect_seq(self)
  }
}

impl<'de, T: Deserialize<'de>, N: ArrayLength> Deserialize<'de> for GenericArrayDeque<T, N> {
  fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
  where
    D: Deserializer<'de>,
  {
    struct SeqVisitor<T, N: ArrayLength> {
      marker: PhantomData<(T, N)>,
    }

    impl<'de, T, N: ArrayLength> Visitor<'de> for SeqVisitor<T, N>
    where
      T: Deserialize<'de>,
    {
      type Value = GenericArrayDeque<T, N>;

      fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("a sequence")
      }

      #[inline]
      fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
      where
        A: SeqAccess<'de>,
      {
        let mut values = GenericArrayDeque::<T, N>::new();

        while let Some(value) = seq.next_element()? {
          if values.push_back(value).is_some() {
            return Err(Error::custom("sequence length exceeds capacity"));
          }
        }

        Ok(values)
      }
    }

    let visitor = SeqVisitor {
      marker: PhantomData,
    };
    deserializer.deserialize_seq(visitor)
  }

  fn deserialize_in_place<D>(deserializer: D, place: &mut Self) -> Result<(), D::Error>
  where
    D: Deserializer<'de>,
  {
    struct SeqInPlaceVisitor<'a, T, N: ArrayLength>(&'a mut GenericArrayDeque<T, N>);

    impl<'de, T, N: ArrayLength> Visitor<'de> for SeqInPlaceVisitor<'_, T, N>
    where
      T: Deserialize<'de>,
    {
      type Value = ();

      fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("a sequence")
      }

      #[inline]
      fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
      where
        A: SeqAccess<'de>,
      {
        self.0.clear();

        while let Some(value) = seq.next_element()? {
          if self.0.push_back(value).is_some() {
            return Err(Error::custom("sequence length exceeds capacity"));
          }
        }

        Ok(())
      }
    }

    deserializer.deserialize_seq(SeqInPlaceVisitor(place))
  }
}
