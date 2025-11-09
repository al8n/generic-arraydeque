#![cfg(feature = "serde")]

use generic_arraydeque::{typenum::U4, GenericArrayDeque};
use serde_test::{assert_de_tokens, assert_de_tokens_error, assert_tokens, Token};

#[test]
fn serialize_roundtrip() {
  let mut deque = GenericArrayDeque::<u32, U4>::new();
  deque.push_back(10);
  deque.push_back(20);
  deque.push_back(30);

  assert_tokens(
    &deque,
    &[
      Token::Seq { len: Some(3) },
      Token::U32(10),
      Token::U32(20),
      Token::U32(30),
      Token::SeqEnd,
    ],
  );

  assert_de_tokens(
    &GenericArrayDeque::<u32, U4>::try_from_array([10, 20, 30]).unwrap(),
    &[
      Token::Seq { len: Some(3) },
      Token::U32(10),
      Token::U32(20),
      Token::U32(30),
      Token::SeqEnd,
    ],
  );
}

#[test]
fn deserialize_overflow() {
  assert_de_tokens_error::<GenericArrayDeque<u8, U4>>(
    &[
      Token::Seq { len: Some(5) },
      Token::U8(1),
      Token::U8(2),
      Token::U8(3),
      Token::U8(4),
      Token::U8(5),
      Token::SeqEnd,
    ],
    "sequence length exceeds capacity",
  );
}
