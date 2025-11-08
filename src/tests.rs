#[cfg(any(feature = "alloc", feature = "std"))]
use std::{vec, vec::Vec};

use generic_array::typenum::*;

use super::*;

#[cfg(feature = "std")]
macro_rules! struct_with_counted_drop {
    ($struct_name:ident $(( $( $elt_ty:ty ),+ ))?, $drop_counter:ident $( => $drop_stmt:expr )? ) => {
        thread_local! {static $drop_counter: ::core::cell::Cell<u32> = ::core::cell::Cell::new(0);}

        #[derive(Clone, Debug, PartialEq)]
        struct $struct_name $(( $( $elt_ty ),+ ))?;

        impl ::std::ops::Drop for $struct_name {
            fn drop(&mut self) {
                $drop_counter.set($drop_counter.get() + 1);

                $($drop_stmt(self))?
            }
        }
    };
    ($struct_name:ident $(( $( $elt_ty:ty ),+ ))?, $drop_counter:ident[ $drop_key:expr,$key_ty:ty ] $( => $drop_stmt:expr )? ) => {
        thread_local! {
            static $drop_counter: ::core::cell::RefCell<::std::collections::HashMap<$key_ty, u32>> =
                ::core::cell::RefCell::new(::std::collections::HashMap::new());
        }

        #[derive(Clone, Debug, PartialEq)]
        struct $struct_name $(( $( $elt_ty ),+ ))?;

        impl ::std::ops::Drop for $struct_name {
            fn drop(&mut self) {
                $drop_counter.with_borrow_mut(|counter| {
                    *counter.entry($drop_key(self)).or_default() += 1;
                });

                $($drop_stmt(self))?
            }
        }
    };
}

#[test]
fn test_swap_front_back_remove() {
  fn test(back: bool) {
    // This test checks that every single combination of tail position and length is tested.
    // Capacity 15 should be large enough to cover every case.
    let mut tester = GenericArrayDeque::<_, U15>::new();
    let usable_cap = tester.capacity();
    let final_len = usable_cap / 2;

    for len in 0..final_len {
      let expected: GenericArrayDeque<_, U15> = if back {
        GenericArrayDeque::try_from_exact_iter(0..len).unwrap()
      } else {
        GenericArrayDeque::try_from_exact_iter((0..len).rev()).unwrap()
      };
      for head_pos in 0..usable_cap {
        tester.head = head_pos;
        tester.len = 0;
        if back {
          for i in 0..len * 2 {
            tester.push_front(i);
          }
          for i in 0..len {
            assert_eq!(tester.swap_remove_back(i), Some(len * 2 - 1 - i));
          }
        } else {
          for i in 0..len * 2 {
            tester.push_back(i);
          }
          for i in 0..len {
            let idx = tester.len() - 1 - i;
            assert_eq!(tester.swap_remove_front(idx), Some(len * 2 - 1 - i));
          }
        }
        assert!(tester.head <= tester.capacity());
        assert!(tester.len <= tester.capacity());
        assert_eq!(tester, expected);
      }
    }
  }
  test(true);
  test(false);
}

#[test]
fn test_insert() {
  // This test checks that every single combination of tail position, length, and
  // insertion position is tested. Capacity 15 should be large enough to cover every case.

  let mut tester = GenericArrayDeque::<_, U15>::new();
  // can't guarantee we got 15, so have to get what we got.
  // 15 would be great, but we will definitely get 2^k - 1, for k >= 4, or else
  // this test isn't covering what it wants to
  let cap = tester.capacity();

  // len is the length *after* insertion
  let minlen = if cfg!(miri) { cap - 1 } else { 1 }; // Miri is too slow
  for len in minlen..cap {
    // 0, 1, 2, .., len - 1
    let expected = GenericArrayDeque::<_, U15>::try_from_iter((0..).take(len)).unwrap();
    for head_pos in 0..cap {
      for to_insert in 0..len {
        tester.head = head_pos;
        tester.len = 0;
        for i in 0..len {
          if i != to_insert {
            tester.push_back(i);
          }
        }
        tester.insert(to_insert, to_insert);
        assert!(tester.head <= tester.capacity());
        assert!(tester.len <= tester.capacity());
        assert_eq!(tester, expected);
      }
    }
  }
}

#[test]
fn test_get() {
  let mut tester = GenericArrayDeque::<_, U5>::new();
  tester.push_back(1);
  tester.push_back(2);
  tester.push_back(3);

  assert_eq!(tester.len(), 3);

  assert_eq!(tester.get(1), Some(&2));
  assert_eq!(tester.get(2), Some(&3));
  assert_eq!(tester.get(0), Some(&1));
  assert_eq!(tester.get(3), None);

  tester.remove(0);

  assert_eq!(tester.len(), 2);
  assert_eq!(tester.get(0), Some(&2));
  assert_eq!(tester.get(1), Some(&3));
  assert_eq!(tester.get(2), None);
}

#[test]
fn test_get_mut() {
  let mut tester = GenericArrayDeque::<_, U5>::new();
  tester.push_back(1);
  tester.push_back(2);
  tester.push_back(3);

  assert_eq!(tester.len(), 3);

  if let Some(elem) = tester.get_mut(0) {
    assert_eq!(*elem, 1);
    *elem = 10;
  }

  if let Some(elem) = tester.get_mut(2) {
    assert_eq!(*elem, 3);
    *elem = 30;
  }

  assert_eq!(tester.get(0), Some(&10));
  assert_eq!(tester.get(2), Some(&30));
  assert_eq!(tester.get_mut(3), None);

  tester.remove(2);

  assert_eq!(tester.len(), 2);
  assert_eq!(tester.get(0), Some(&10));
  assert_eq!(tester.get(1), Some(&2));
  assert_eq!(tester.get(2), None);
}

#[test]
fn test_swap() {
  let mut tester = GenericArrayDeque::<_, U5>::new();
  tester.push_back(1);
  tester.push_back(2);
  tester.push_back(3);

  assert_eq!(tester, [1, 2, 3]);

  tester.swap(0, 0);
  assert_eq!(tester, [1, 2, 3]);
  tester.swap(0, 1);
  assert_eq!(tester, [2, 1, 3]);
  tester.swap(2, 1);
  assert_eq!(tester, [2, 3, 1]);
  tester.swap(1, 2);
  assert_eq!(tester, [2, 1, 3]);
  tester.swap(0, 2);
  assert_eq!(tester, [3, 1, 2]);
  tester.swap(2, 2);
  assert_eq!(tester, [3, 1, 2]);
}

#[test]
#[should_panic = "assertion failed: j < self.len()"]
fn test_swap_panic() {
  let mut tester = GenericArrayDeque::<_, U5>::new();
  tester.push_back(1);
  tester.push_back(2);
  tester.push_back(3);
  tester.swap(2, 3);
}

#[test]
fn test_contains() {
  let mut tester = GenericArrayDeque::<_, U5>::new();
  tester.push_back(1);
  tester.push_back(2);
  tester.push_back(3);

  assert!(tester.contains(&1));
  assert!(tester.contains(&3));
  assert!(!tester.contains(&0));
  assert!(!tester.contains(&4));
  tester.remove(0);
  assert!(!tester.contains(&1));
  assert!(tester.contains(&2));
  assert!(tester.contains(&3));
}

#[test]
fn test_rotate_left_right() {
  let mut tester: GenericArrayDeque<_, U10> = GenericArrayDeque::try_from_iter(1..=10).unwrap();
  assert_eq!(tester.len(), 10);

  tester.rotate_left(0);
  assert_eq!(tester, [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);

  tester.rotate_right(0);
  assert_eq!(tester, [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);

  tester.rotate_left(3);
  assert_eq!(tester, [4, 5, 6, 7, 8, 9, 10, 1, 2, 3]);

  tester.rotate_right(5);
  assert_eq!(tester, [9, 10, 1, 2, 3, 4, 5, 6, 7, 8]);

  tester.rotate_left(tester.len());
  assert_eq!(tester, [9, 10, 1, 2, 3, 4, 5, 6, 7, 8]);

  tester.rotate_right(tester.len());
  assert_eq!(tester, [9, 10, 1, 2, 3, 4, 5, 6, 7, 8]);

  tester.rotate_left(1);
  assert_eq!(tester, [10, 1, 2, 3, 4, 5, 6, 7, 8, 9]);
}

#[test]
#[should_panic = "assertion failed: n <= self.len()"]
fn test_rotate_left_panic() {
  let mut tester: GenericArrayDeque<_, U12> = GenericArrayDeque::try_from_iter(1..=10).unwrap();
  tester.rotate_left(tester.len() + 1);
}

#[test]
#[should_panic = "assertion failed: n <= self.len()"]
fn test_rotate_right_panic() {
  let mut tester: GenericArrayDeque<_, U12> = GenericArrayDeque::try_from_iter(1..=10).unwrap();
  tester.rotate_right(tester.len() + 1);
}

#[test]
fn test_binary_search() {
  // If the given VecDeque is not sorted, the returned result is unspecified and meaningless,
  // as this method performs a binary search.

  let tester: GenericArrayDeque<_, U12> =
    GenericArrayDeque::try_from_iter([0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55]).unwrap();

  assert_eq!(tester.binary_search(&0), Ok(0));
  assert_eq!(tester.binary_search(&5), Ok(5));
  assert_eq!(tester.binary_search(&55), Ok(10));
  assert_eq!(tester.binary_search(&4), Err(5));
  assert_eq!(tester.binary_search(&-1), Err(0));
  assert!(matches!(tester.binary_search(&1), Ok(1..=2)));

  let tester: GenericArrayDeque<_, U15> =
    GenericArrayDeque::try_from_iter([1, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3]).unwrap();
  assert_eq!(tester.binary_search(&1), Ok(0));
  assert!(matches!(tester.binary_search(&2), Ok(1..=4)));
  assert!(matches!(tester.binary_search(&3), Ok(5..=13)));
  assert_eq!(tester.binary_search(&-2), Err(0));
  assert_eq!(tester.binary_search(&0), Err(0));
  assert_eq!(tester.binary_search(&4), Err(14));
  assert_eq!(tester.binary_search(&5), Err(14));
}

#[test]
fn test_binary_search_by() {
  // If the given VecDeque is not sorted, the returned result is unspecified and meaningless,
  // as this method performs a binary search.

  let tester: GenericArrayDeque<_, U12> =
    GenericArrayDeque::try_from_iter([0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55]).unwrap();

  assert_eq!(tester.binary_search_by(|x| x.cmp(&0)), Ok(0));
  assert_eq!(tester.binary_search_by(|x| x.cmp(&5)), Ok(5));
  assert_eq!(tester.binary_search_by(|x| x.cmp(&55)), Ok(10));
  assert_eq!(tester.binary_search_by(|x| x.cmp(&4)), Err(5));
  assert_eq!(tester.binary_search_by(|x| x.cmp(&-1)), Err(0));
  assert!(matches!(tester.binary_search_by(|x| x.cmp(&1)), Ok(1..=2)));
}

#[test]
fn test_binary_search_key() {
  // If the given VecDeque is not sorted, the returned result is unspecified and meaningless,
  // as this method performs a binary search.

  let tester: GenericArrayDeque<_, U15> = GenericArrayDeque::try_from_iter([
    (-1, 0),
    (2, 10),
    (6, 5),
    (7, 1),
    (8, 10),
    (10, 2),
    (20, 3),
    (24, 5),
    (25, 18),
    (28, 13),
    (31, 21),
    (32, 4),
    (54, 25),
  ])
  .unwrap();

  assert_eq!(tester.binary_search_by_key(&-1, |&(a, _b)| a), Ok(0));
  assert_eq!(tester.binary_search_by_key(&8, |&(a, _b)| a), Ok(4));
  assert_eq!(tester.binary_search_by_key(&25, |&(a, _b)| a), Ok(8));
  assert_eq!(tester.binary_search_by_key(&54, |&(a, _b)| a), Ok(12));
  assert_eq!(tester.binary_search_by_key(&-2, |&(a, _b)| a), Err(0));
  assert_eq!(tester.binary_search_by_key(&1, |&(a, _b)| a), Err(1));
  assert_eq!(tester.binary_search_by_key(&4, |&(a, _b)| a), Err(2));
  assert_eq!(tester.binary_search_by_key(&13, |&(a, _b)| a), Err(6));
  assert_eq!(tester.binary_search_by_key(&55, |&(a, _b)| a), Err(13));
  assert_eq!(tester.binary_search_by_key(&100, |&(a, _b)| a), Err(13));

  let tester: GenericArrayDeque<_, U15> = GenericArrayDeque::try_from_iter([
    (0, 0),
    (2, 1),
    (6, 1),
    (5, 1),
    (3, 1),
    (1, 2),
    (2, 3),
    (4, 5),
    (5, 8),
    (8, 13),
    (1, 21),
    (2, 34),
    (4, 55),
  ])
  .unwrap();

  assert_eq!(tester.binary_search_by_key(&0, |&(_a, b)| b), Ok(0));
  assert!(matches!(
    tester.binary_search_by_key(&1, |&(_a, b)| b),
    Ok(1..=4)
  ));
  assert_eq!(tester.binary_search_by_key(&8, |&(_a, b)| b), Ok(8));
  assert_eq!(tester.binary_search_by_key(&13, |&(_a, b)| b), Ok(9));
  assert_eq!(tester.binary_search_by_key(&55, |&(_a, b)| b), Ok(12));
  assert_eq!(tester.binary_search_by_key(&-1, |&(_a, b)| b), Err(0));
  assert_eq!(tester.binary_search_by_key(&4, |&(_a, b)| b), Err(7));
  assert_eq!(tester.binary_search_by_key(&56, |&(_a, b)| b), Err(13));
  assert_eq!(tester.binary_search_by_key(&100, |&(_a, b)| b), Err(13));
}

#[test]
fn make_contiguous_big_head() {
  let mut tester = GenericArrayDeque::<_, U15>::new();

  for i in 0..3 {
    tester.push_back(i);
  }

  for i in 3..10 {
    tester.push_front(i);
  }

  // 012......9876543
  assert_eq!(tester.capacity(), 15);
  assert_eq!(
    (&[9, 8, 7, 6, 5, 4, 3] as &[_], &[0, 1, 2] as &[_]),
    tester.as_slices()
  );

  let expected_start = tester.as_slices().1.len();
  tester.make_contiguous();
  assert_eq!(tester.head, expected_start);
  assert_eq!(
    (&[9, 8, 7, 6, 5, 4, 3, 0, 1, 2] as &[_], &[] as &[_]),
    tester.as_slices()
  );
}

#[test]
fn make_contiguous_big_tail() {
  let mut tester = GenericArrayDeque::<_, U15>::new();

  for i in 0..8 {
    tester.push_back(i);
  }

  for i in 8..10 {
    tester.push_front(i);
  }

  // 01234567......98
  let expected_start = 0;
  tester.make_contiguous();
  assert_eq!(tester.head, expected_start);
  assert_eq!(
    (&[9, 8, 0, 1, 2, 3, 4, 5, 6, 7] as &[_], &[] as &[_]),
    tester.as_slices()
  );
}

#[test]
fn make_contiguous_small_free() {
  let mut tester = GenericArrayDeque::<_, U16>::new();

  for i in b'A'..b'I' {
    tester.push_back(i as char);
  }

  for i in b'I'..b'N' {
    tester.push_front(i as char);
  }

  assert_eq!(
    tester,
    ['M', 'L', 'K', 'J', 'I', 'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H']
  );

  // ABCDEFGH...MLKJI
  let expected_start = 0;
  tester.make_contiguous();
  assert_eq!(tester.head, expected_start);
  assert_eq!(
    (
      &['M', 'L', 'K', 'J', 'I', 'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H'] as &[_],
      &[] as &[_]
    ),
    tester.as_slices()
  );

  tester.clear();
  for i in b'I'..b'N' {
    tester.push_back(i as char);
  }

  for i in b'A'..b'I' {
    tester.push_front(i as char);
  }

  // IJKLM...HGFEDCBA
  let expected_start = 3;
  tester.make_contiguous();
  assert_eq!(tester.head, expected_start);
  assert_eq!(
    (
      &['H', 'G', 'F', 'E', 'D', 'C', 'B', 'A', 'I', 'J', 'K', 'L', 'M'] as &[_],
      &[] as &[_]
    ),
    tester.as_slices()
  );
}

#[test]
fn make_contiguous_head_to_end() {
  let mut tester = GenericArrayDeque::<_, U16>::new();

  for i in b'A'..b'L' {
    tester.push_back(i as char);
  }

  for i in b'L'..b'Q' {
    tester.push_front(i as char);
  }

  assert_eq!(
    tester,
    ['P', 'O', 'N', 'M', 'L', 'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K']
  );

  // ABCDEFGHIJKPONML
  let expected_start = 0;
  tester.make_contiguous();
  assert_eq!(tester.head, expected_start);
  assert_eq!(
    (
      &['P', 'O', 'N', 'M', 'L', 'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K'] as &[_],
      &[] as &[_]
    ),
    tester.as_slices()
  );

  tester.clear();
  for i in b'L'..b'Q' {
    tester.push_back(i as char);
  }

  for i in b'A'..b'L' {
    tester.push_front(i as char);
  }

  // LMNOPKJIHGFEDCBA
  let expected_start = 0;
  tester.make_contiguous();
  assert_eq!(tester.head, expected_start);
  assert_eq!(
    (
      &['K', 'J', 'I', 'H', 'G', 'F', 'E', 'D', 'C', 'B', 'A', 'L', 'M', 'N', 'O', 'P'] as &[_],
      &[] as &[_]
    ),
    tester.as_slices()
  );
}

#[cfg(any(feature = "alloc", feature = "std"))]
#[test]
fn make_contiguous_head_to_end_2() {
  // Another test case for #79808, taken from #80293.

  let mut dq = GenericArrayDeque::<_, U6>::try_from_iter(0..6).unwrap();
  dq.pop_front();
  dq.pop_front();
  dq.push_back(6);
  dq.push_back(7);
  dq.push_back(8);
  dq.make_contiguous();
  let collected: Vec<_> = dq.iter().copied().collect();
  assert_eq!(dq.as_slices(), (&collected[..], &[] as &[_]));
}

#[test]
fn test_remove() {
  // This test checks that every single combination of tail position, length, and
  // removal position is tested. Capacity 15 should be large enough to cover every case.

  let mut tester = GenericArrayDeque::<_, U15>::new();
  // can't guarantee we got 15, so have to get what we got.
  // 15 would be great, but we will definitely get 2^k - 1, for k >= 4, or else
  // this test isn't covering what it wants to
  let cap = tester.capacity();

  // len is the length *after* removal
  let minlen = if cfg!(miri) { cap - 2 } else { 0 }; // Miri is too slow
  for len in minlen..cap - 1 {
    // 0, 1, 2, .., len - 1
    let expected = GenericArrayDeque::<_, U15>::try_from_iter((0..).take(len)).unwrap();
    for head_pos in 0..cap {
      for to_remove in 0..=len {
        tester.head = head_pos;
        tester.len = 0;
        for i in 0..len {
          if i == to_remove {
            tester.push_back(1234);
          }
          tester.push_back(i);
        }
        if to_remove == len {
          tester.push_back(1234);
        }
        tester.remove(to_remove);
        assert!(tester.head <= tester.capacity());
        assert!(tester.len <= tester.capacity());
        assert_eq!(tester, expected);
      }
    }
  }
}

#[test]
fn test_range() {
  let mut tester: GenericArrayDeque<_, U7> = GenericArrayDeque::new();

  let cap = tester.capacity();
  let minlen = if cfg!(miri) { cap - 1 } else { 0 }; // Miri is too slow
  for len in minlen..=cap {
    for head in 0..=cap {
      for start in 0..=len {
        for end in start..=len {
          tester.head = head;
          tester.len = 0;
          for i in 0..len {
            tester.push_back(i);
          }

          // Check that we iterate over the correct values
          let range: GenericArrayDeque<_, U7> =
            GenericArrayDeque::try_from_iter(tester.range(start..end).copied()).unwrap();
          let expected: GenericArrayDeque<_, U7> =
            GenericArrayDeque::try_from_iter(start..end).unwrap();
          assert_eq!(range, expected);
        }
      }
    }
  }
}

#[test]
fn test_range_mut() {
  let mut tester: GenericArrayDeque<_, U7> = GenericArrayDeque::new();

  let cap = tester.capacity();
  for len in 0..=cap {
    for head in 0..=cap {
      for start in 0..=len {
        for end in start..=len {
          tester.head = head;
          tester.len = 0;
          for i in 0..len {
            tester.push_back(i);
          }

          let head_was = tester.head;
          let len_was = tester.len;

          // Check that we iterate over the correct values
          let range: GenericArrayDeque<_, U7> =
            GenericArrayDeque::try_from_iter(tester.range_mut(start..end).map(|v| *v)).unwrap();
          let expected: GenericArrayDeque<_, U7> =
            GenericArrayDeque::try_from_iter(start..end).unwrap();
          assert_eq!(range, expected);

          // We shouldn't have changed the capacity or made the
          // head or tail out of bounds
          assert_eq!(tester.capacity(), cap);
          assert_eq!(tester.head, head_was);
          assert_eq!(tester.len, len_was);
        }
      }
    }
  }
}

#[test]
fn test_drain() {
  let mut tester: GenericArrayDeque<_, U7> = GenericArrayDeque::new();

  let cap = tester.capacity();
  for len in 0..=cap {
    for head in 0..cap {
      for drain_start in 0..=len {
        for drain_end in drain_start..=len {
          tester.head = head;
          tester.len = 0;
          for i in 0..len {
            tester.push_back(i);
          }

          // Check that we drain the correct values
          let drained: GenericArrayDeque<_, U7> =
            GenericArrayDeque::try_from_iter(tester.drain(drain_start..drain_end)).unwrap();
          let drained_expected: GenericArrayDeque<_, U7> =
            GenericArrayDeque::try_from_iter(drain_start..drain_end).unwrap();
          assert_eq!(drained, drained_expected);

          // We shouldn't have changed the capacity or made the
          // head or tail out of bounds
          assert_eq!(tester.capacity(), cap);
          assert!(tester.head <= tester.capacity());
          assert!(tester.len <= tester.capacity());

          // We should see the correct values in the GenericArrayDeque
          let expected: GenericArrayDeque<_, U14> =
            GenericArrayDeque::try_from_iter((0..drain_start).chain(drain_end..len)).unwrap();
          assert_eq!(expected, tester);
        }
      }
    }
  }
}

#[cfg(any(feature = "alloc", feature = "std"))]
#[test]
fn issue_108453() {
  let mut deque = GenericArrayDeque::<_, U10>::new();

  deque.push_back(1u8);
  deque.push_back(2);
  deque.push_back(3);

  deque.push_front(10);
  deque.push_front(9);

  assert_eq!(deque.into_iter().collect::<Vec<_>>(), vec![9, 10, 1, 2, 3]);
}

#[test]
fn test_split_off() {
  // This test checks that every single combination of tail position, length, and
  // split position is tested. Capacity 15 should be large enough to cover every case.

  let mut tester = GenericArrayDeque::<_, U15>::new();
  // can't guarantee we got 15, so have to get what we got.
  // 15 would be great, but we will definitely get 2^k - 1, for k >= 4, or else
  // this test isn't covering what it wants to
  let cap = tester.capacity();

  // len is the length *before* splitting
  let minlen = if cfg!(miri) { cap - 1 } else { 0 }; // Miri is too slow
  for len in minlen..cap {
    // index to split at
    for at in 0..=len {
      // 0, 1, 2, .., at - 1 (may be empty)
      let expected_self = GenericArrayDeque::<_, U15>::try_from_iter((0..).take(at)).unwrap();
      // at, at + 1, .., len - 1 (may be empty)
      let expected_other =
        GenericArrayDeque::<_, U15>::try_from_iter((at..).take(len - at)).unwrap();

      for head_pos in 0..cap {
        tester.head = head_pos;
        tester.len = 0;
        for i in 0..len {
          tester.push_back(i);
        }
        let result = tester.split_off(at);
        assert!(tester.head <= tester.capacity());
        assert!(tester.len <= tester.capacity());
        assert!(result.head <= result.capacity());
        assert!(result.len <= result.capacity());
        assert_eq!(tester, expected_self);
        assert_eq!(result, expected_other);
      }
    }
  }
}

#[cfg(any(feature = "alloc", feature = "std"))]
#[test]
fn test_from_vec() {
  use std::vec::Vec;

  for cap in 0..35 {
    for len in 0..=cap {
      let mut vec = Vec::with_capacity(cap);
      vec.extend(0..len);

      let vd = GenericArrayDeque::<_, U40>::try_from_vec(vec.clone()).unwrap();
      assert_eq!(vd.len(), vec.len());
      assert!(vd.into_iter().eq(vec));
    }
  }
}

#[test]
fn test_extend_basic() {
  test_extend_impl(false);
}

#[test]
fn test_extend_trusted_len() {
  test_extend_impl(true);
}

fn test_extend_impl(trusted_len: bool) {
  struct VecDequeTester {
    test: GenericArrayDeque<usize, Sum<U8192, U4>>,
    expected: GenericArrayDeque<usize, Sum<U8192, U4>>,
    trusted_len: bool,
  }

  impl VecDequeTester {
    fn new(trusted_len: bool) -> Self {
      Self {
        test: GenericArrayDeque::new(),
        expected: GenericArrayDeque::new(),
        trusted_len,
      }
    }

    fn test_extend<I>(&mut self, iter: I)
    where
      I: Iterator<Item = usize> + ExactSizeIterator + Clone,
    {
      struct BasicIterator<I>(I);
      impl<I> Iterator for BasicIterator<I>
      where
        I: Iterator<Item = usize>,
      {
        type Item = usize;

        fn next(&mut self) -> Option<Self::Item> {
          self.0.next()
        }
      }

      if self.trusted_len {
        self.test.try_extend_from_exact_iter(iter.clone());
      } else {
        self.test.try_extend_from_iter(BasicIterator(iter.clone()));
      }

      for item in iter {
        self.expected.push_back(item);
      }

      assert_eq!(self.test, self.expected);
    }

    fn drain<R: RangeBounds<usize> + Clone>(&mut self, range: R) {
      self.test.drain(range.clone());
      self.expected.drain(range);

      assert_eq!(self.test, self.expected);
    }

    fn clear(&mut self) {
      self.test.clear();
      self.expected.clear();
    }

    fn remaining_capacity(&self) -> usize {
      self.test.capacity() - self.test.len()
    }
  }

  let mut tester = VecDequeTester::new(trusted_len);

  // Initial capacity
  tester.test_extend(0..tester.remaining_capacity());

  // Grow
  tester.test_extend(1024..2048);

  // Wrap around
  tester.drain(..128);

  tester.test_extend(0..tester.remaining_capacity());

  // Continue
  tester.drain(256..);
  tester.test_extend(4096..8196);

  tester.clear();

  // Start again
  tester.test_extend(0..32);
}

#[test]
fn test_from_array() {
  fn test<N: ArrayLength>() {
    let mut array: GenericArray<usize, N> = GenericArray::default();

    for i in 0..N::USIZE {
      array[i] = i;
    }

    let deq: GenericArrayDeque<_, N> = array.into();

    for i in 0..N::USIZE {
      assert_eq!(deq[i], i);
    }

    assert_eq!(deq.len(), N::USIZE);
  }
  test::<U0>();
  test::<U1>();
  test::<U2>();
  test::<U32>();
  test::<U35>();
}

#[test]
#[cfg(any(feature = "alloc", feature = "std"))]
fn test_vec_from_vecdeque() {
  fn create_vec_and_test_convert<CAP: ArrayLength>(offset: usize, len: usize) {
    let mut vd = GenericArrayDeque::<_, CAP>::new();
    for _ in 0..offset {
      vd.push_back(0);
      vd.pop_front();
    }
    let _ = vd.try_extend_from_iter(0..len);

    let vec: Vec<_> = Vec::from(vd.clone());
    assert_eq!(vec.len(), vd.len());
    assert!(vec.into_iter().eq(vd));
  }

  // Miri is too slow
  let max_pwr = if cfg!(miri) { 5 } else { 7 };

  for cap_pwr in 0..max_pwr {
    // Make capacity as a (2^x)-1, so that the ring size is 2^x
    let cap = (2i32.pow(cap_pwr) - 1) as usize;

    // In these cases there is enough free space to solve it with copies
    for len in 0..cap.div_ceil(2) {
      // Test contiguous cases
      for offset in 0..(cap - len) {
        if cfg!(miri) {
          create_vec_and_test_convert::<U5>(offset, len);
        } else {
          create_vec_and_test_convert::<U7>(offset, len);
        }
      }

      // Test cases where block at end of buffer is bigger than block at start
      for offset in (cap - len)..(cap - (len / 2)) {
        if cfg!(miri) {
          create_vec_and_test_convert::<U5>(offset, len);
        } else {
          create_vec_and_test_convert::<U7>(offset, len);
        }
      }

      // Test cases where block at start of buffer is bigger than block at end
      for offset in (cap - (len / 2))..cap {
        if cfg!(miri) {
          create_vec_and_test_convert::<U5>(offset, len);
        } else {
          create_vec_and_test_convert::<U7>(offset, len);
        }
      }
    }

    // Now there's not (necessarily) space to straighten the ring with simple copies,
    // the ring will use swapping when:
    // (cap + 1 - offset) > (cap + 1 - len) && (len - (cap + 1 - offset)) > (cap + 1 - len))
    //  right block size  >   free space    &&      left block size       >    free space
    for len in cap.div_ceil(2)..cap {
      // Test contiguous cases
      for offset in 0..(cap - len) {
        if cfg!(miri) {
          create_vec_and_test_convert::<U5>(offset, len);
        } else {
          create_vec_and_test_convert::<U7>(offset, len);
        }
      }

      // Test cases where block at end of buffer is bigger than block at start
      for offset in (cap - len)..(cap - (len / 2)) {
        if cfg!(miri) {
          create_vec_and_test_convert::<U5>(offset, len);
        } else {
          create_vec_and_test_convert::<U7>(offset, len);
        }
      }

      // Test cases where block at start of buffer is bigger than block at end
      for offset in (cap - (len / 2))..cap {
        if cfg!(miri) {
          create_vec_and_test_convert::<U5>(offset, len);
        } else {
          create_vec_and_test_convert::<U7>(offset, len);
        }
      }
    }
  }
}

#[test]
#[cfg(any(feature = "alloc", feature = "std"))]
fn test_clone_from() {
  let m = vec![1; 8];
  let n = vec![2; 12];
  let limit = if cfg!(miri) { 4 } else { 8 }; // Miri is too slow
  for pfv in 0..limit {
    for pfu in 0..limit {
      for longer in 0..2 {
        let (vr, ur) = if longer == 0 { (&m, &n) } else { (&n, &m) };
        let mut v = GenericArrayDeque::<_, U12>::try_from(vr.clone()).unwrap();
        for _ in 0..pfv {
          v.push_front(1);
        }
        let mut u = GenericArrayDeque::<_, U12>::try_from(ur.clone()).unwrap();
        for _ in 0..pfu {
          u.push_front(2);
        }
        v.clone_from(&u);
        assert_eq!(&v, &u);
      }
    }
  }
}

#[cfg(feature = "std")]
#[test]
fn test_vec_deque_truncate_drop() {
  struct_with_counted_drop!(Elem, DROPS);

  const LEN: usize = 5;
  for push_front in 0..=LEN {
    let mut tester = GenericArrayDeque::<Elem, U5>::new();
    for index in 0..LEN {
      if index < push_front {
        tester.push_front(Elem);
      } else {
        tester.push_back(Elem);
      }
    }
    assert_eq!(DROPS.get(), 0);
    tester.truncate(3);
    assert_eq!(DROPS.get(), 2);
    tester.truncate(0);
    assert_eq!(DROPS.get(), 5);
    DROPS.set(0);
  }
}

#[cfg(any(feature = "alloc", feature = "std"))]
#[test]
fn issue_53529() {
  use std::boxed::Box;

  let mut dst = GenericArrayDeque::<_, U4>::new();
  dst.push_front(Box::new(1));
  dst.push_front(Box::new(2));
  assert_eq!(*dst.pop_back().unwrap(), 1);

  let mut src = GenericArrayDeque::<_, U4>::new();
  src.push_front(Box::new(2));
  dst.append(&mut src);
  for a in dst {
    assert_eq!(*a, 2);
  }
}

#[test]
fn issue_80303() {
  use core::iter;
  use core::num::Wrapping;

  // This is a valid, albeit rather bad hash function implementation.
  struct SimpleHasher(Wrapping<u64>);

  impl Hasher for SimpleHasher {
    fn finish(&self) -> u64 {
      self.0 .0
    }

    fn write(&mut self, bytes: &[u8]) {
      // This particular implementation hashes value 24 in addition to bytes.
      // Such an implementation is valid as Hasher only guarantees equivalence
      // for the exact same set of calls to its methods.
      for &v in iter::once(&24).chain(bytes) {
        self.0 = Wrapping(31) * self.0 + Wrapping(u64::from(v));
      }
    }
  }

  fn hash_code(value: impl Hash) -> u64 {
    let mut hasher = SimpleHasher(Wrapping(1));
    value.hash(&mut hasher);
    hasher.finish()
  }

  // This creates two deques for which values returned by as_slices
  // method differ.
  let vda = GenericArrayDeque::<u8, U10>::try_from_exact_iter(0..10).unwrap();
  let mut vdb = GenericArrayDeque::<u8, U10>::new();
  assert!(vdb.try_extend_from_iter(5..10).is_none());
  (0..5).rev().for_each(|elem| {
    assert!(vdb.push_front(elem).is_none());
  });
  assert_ne!(vda.as_slices(), vdb.as_slices());
  assert_eq!(vda, vdb);
  assert_eq!(hash_code(vda), hash_code(vdb));
}

#[cfg(all(any(feature = "alloc", feature = "std"), feature = "unstable"))]
#[test]
fn extract_if_test() {
  let mut m = GenericArrayDeque::<u32, U24>::try_from_exact_iter([1, 2, 3, 4, 5, 6]).unwrap();
  let deleted = m.extract_if(.., |v| *v < 4).collect::<Vec<_>>();

  assert_eq!(deleted, &[1, 2, 3]);
  assert_eq!(m, &[4, 5, 6]);
}

#[cfg(all(any(feature = "alloc", feature = "std"), feature = "unstable"))]
#[test]
fn drain_to_empty_test() {
  let mut m = GenericArrayDeque::<u32, U24>::try_from_exact_iter([1, 2, 3, 4, 5, 6]).unwrap();
  let deleted = m.extract_if(.., |_| true).collect::<Vec<u32>>();

  assert_eq!(deleted, &[1, 2, 3, 4, 5, 6]);
  assert_eq!(m, &[]);
}

#[cfg(feature = "unstable")]
#[test]
fn extract_if_empty() {
  let mut list = GenericArrayDeque::<usize, U4>::new();

  {
    let mut iter = list.extract_if(.., |_| true);
    assert_eq!(iter.size_hint(), (0, Some(0)));
    assert_eq!(iter.next(), None);
    assert_eq!(iter.size_hint(), (0, Some(0)));
    assert_eq!(iter.next(), None);
    assert_eq!(iter.size_hint(), (0, Some(0)));
  }

  assert_eq!(list.len(), 0);
  #[cfg(any(feature = "alloc", feature = "std"))]
  assert_eq!(list, vec![]);
}

#[cfg(feature = "unstable")]
#[test]
fn extract_if_zst() {
  let mut list = GenericArrayDeque::<_, U24>::try_from_exact_iter([(), (), (), (), ()]).unwrap();
  let initial_len = list.len();
  let mut count = 0;

  {
    let mut iter = list.extract_if(.., |_| true);
    assert_eq!(iter.size_hint(), (0, Some(initial_len)));
    while let Some(_) = iter.next() {
      count += 1;
      assert_eq!(iter.size_hint(), (0, Some(initial_len - count)));
    }
    assert_eq!(iter.size_hint(), (0, Some(0)));
    assert_eq!(iter.next(), None);
    assert_eq!(iter.size_hint(), (0, Some(0)));
  }

  assert_eq!(count, initial_len);
  assert_eq!(list.len(), 0);

  #[cfg(any(feature = "alloc", feature = "std"))]
  assert_eq!(list, vec![]);
}

#[cfg(feature = "unstable")]
#[test]
fn extract_if_false() {
  let mut list =
    GenericArrayDeque::<_, U15>::try_from_exact_iter([1, 2, 3, 4, 5, 6, 7, 8, 9, 10]).unwrap();

  let initial_len = list.len();
  let mut count = 0;

  {
    let mut iter = list.extract_if(.., |_| false);
    assert_eq!(iter.size_hint(), (0, Some(initial_len)));
    for _ in iter.by_ref() {
      count += 1;
    }
    assert_eq!(iter.size_hint(), (0, Some(0)));
    assert_eq!(iter.next(), None);
    assert_eq!(iter.size_hint(), (0, Some(0)));
  }

  assert_eq!(count, 0);
  assert_eq!(list.len(), initial_len);
  #[cfg(any(feature = "alloc", feature = "std"))]
  assert_eq!(list, vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
}

#[cfg(feature = "unstable")]
#[test]
fn extract_if_true() {
  let mut list =
    GenericArrayDeque::<_, U15>::try_from_exact_iter([1, 2, 3, 4, 5, 6, 7, 8, 9, 10]).unwrap();

  let initial_len = list.len();
  let mut count = 0;

  {
    let mut iter = list.extract_if(.., |_| true);
    assert_eq!(iter.size_hint(), (0, Some(initial_len)));
    while let Some(_) = iter.next() {
      count += 1;
      assert_eq!(iter.size_hint(), (0, Some(initial_len - count)));
    }
    assert_eq!(iter.size_hint(), (0, Some(0)));
    assert_eq!(iter.next(), None);
    assert_eq!(iter.size_hint(), (0, Some(0)));
  }

  assert_eq!(count, initial_len);
  assert_eq!(list.len(), 0);
  #[cfg(any(feature = "alloc", feature = "std"))]
  assert_eq!(list, vec![]);
}

#[cfg(all(any(feature = "alloc", feature = "std"), feature = "unstable"))]
#[test]
fn extract_if_non_contiguous() {
  use std::{vec, vec::Vec};

  let mut list = GenericArrayDeque::<_, U24>::try_from_exact_iter([
    1, 2, 4, 6, 7, 9, 11, 13, 15, 17, 18, 20, 22, 24, 26, 27, 29, 31, 33, 34, 35, 36, 37, 39,
  ])
  .unwrap();
  list.rotate_left(3);

  assert!(!list.is_contiguous());
  assert_eq!(
    list,
    [6, 7, 9, 11, 13, 15, 17, 18, 20, 22, 24, 26, 27, 29, 31, 33, 34, 35, 36, 37, 39, 1, 2, 4]
  );

  let removed = list.extract_if(.., |x| *x % 2 == 0).collect::<Vec<_>>();
  assert_eq!(removed.len(), 10);
  assert_eq!(removed, vec![6, 18, 20, 22, 24, 26, 34, 36, 2, 4]);

  assert_eq!(list.len(), 14);
  assert_eq!(
    list,
    vec![7, 9, 11, 13, 15, 17, 27, 29, 31, 33, 35, 37, 39, 1]
  );
}

#[cfg(all(any(feature = "alloc", feature = "std"), feature = "unstable"))]
#[test]
fn extract_if_complex() {
  use std::{vec, vec::Vec};

  {
    //                [+xxx++++++xxxxx++++x+x++]
    let mut list = GenericArrayDeque::<_, U32>::try_from_exact_iter([
      1, 2, 4, 6, 7, 9, 11, 13, 15, 17, 18, 20, 22, 24, 26, 27, 29, 31, 33, 34, 35, 36, 37, 39,
    ])
    .unwrap();

    let removed = list.extract_if(.., |x| *x % 2 == 0).collect::<Vec<_>>();
    assert_eq!(removed.len(), 10);
    assert_eq!(removed, vec![2, 4, 6, 18, 20, 22, 24, 26, 34, 36]);

    assert_eq!(list.len(), 14);
    assert_eq!(
      list,
      vec![1, 7, 9, 11, 13, 15, 17, 27, 29, 31, 33, 35, 37, 39]
    );
  }

  {
    // [xxx++++++xxxxx++++x+x++]
    let mut list = GenericArrayDeque::<_, U24>::try_from_exact_iter([
      2, 4, 6, 7, 9, 11, 13, 15, 17, 18, 20, 22, 24, 26, 27, 29, 31, 33, 34, 35, 36, 37, 39,
    ])
    .unwrap();

    let removed = list.extract_if(.., |x| *x % 2 == 0).collect::<Vec<_>>();
    assert_eq!(removed.len(), 10);
    assert_eq!(removed, vec![2, 4, 6, 18, 20, 22, 24, 26, 34, 36]);

    assert_eq!(list.len(), 13);
    assert_eq!(list, vec![7, 9, 11, 13, 15, 17, 27, 29, 31, 33, 35, 37, 39]);
  }

  {
    // [xxx++++++xxxxx++++x+x]
    let mut list = GenericArrayDeque::<_, U24>::try_from_exact_iter([
      2, 4, 6, 7, 9, 11, 13, 15, 17, 18, 20, 22, 24, 26, 27, 29, 31, 33, 34, 35, 36,
    ])
    .unwrap();

    let removed = list.extract_if(.., |x| *x % 2 == 0).collect::<Vec<_>>();
    assert_eq!(removed.len(), 10);
    assert_eq!(removed, vec![2, 4, 6, 18, 20, 22, 24, 26, 34, 36]);

    assert_eq!(list.len(), 11);
    assert_eq!(list, vec![7, 9, 11, 13, 15, 17, 27, 29, 31, 33, 35]);
  }

  {
    // [xxxxxxxxxx+++++++++++]
    let mut list = GenericArrayDeque::<_, U24>::try_from_exact_iter([
      2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 1, 3, 5, 7, 9, 11, 13, 15, 17, 19,
    ])
    .unwrap();

    let removed = list.extract_if(.., |x| *x % 2 == 0).collect::<Vec<_>>();
    assert_eq!(removed.len(), 10);
    assert_eq!(removed, vec![2, 4, 6, 8, 10, 12, 14, 16, 18, 20]);

    assert_eq!(list.len(), 10);
    assert_eq!(list, vec![1, 3, 5, 7, 9, 11, 13, 15, 17, 19]);
  }

  {
    // [+++++++++++xxxxxxxxxx]
    let mut list = GenericArrayDeque::<_, U24>::try_from_exact_iter([
      1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20,
    ])
    .unwrap();

    let removed = list.extract_if(.., |x| *x % 2 == 0).collect::<Vec<_>>();
    assert_eq!(removed.len(), 10);
    assert_eq!(removed, vec![2, 4, 6, 8, 10, 12, 14, 16, 18, 20]);

    assert_eq!(list.len(), 10);
    assert_eq!(list, vec![1, 3, 5, 7, 9, 11, 13, 15, 17, 19]);
  }
}

#[cfg(all(feature = "std", feature = "unstable"))]
#[test]
#[cfg_attr(not(panic = "unwind"), ignore = "test requires unwinding support")]
fn extract_if_drop_panic_leak() {
  use core::sync::atomic::{AtomicUsize, Ordering::SeqCst};
  use std::panic::{catch_unwind, AssertUnwindSafe};

  /// A blueprint for crash test dummy instances that monitor particular events.
  /// Some instances may be configured to panic at some point.
  /// Events are `clone`, `drop` or some anonymous `query`.
  ///
  /// Crash test dummies are identified and ordered by an id, so they can be used
  /// as keys in a BTreeMap.
  #[derive(Debug)]
  pub(crate) struct CrashTestDummy {
    pub id: usize,
    cloned: AtomicUsize,
    dropped: AtomicUsize,
    queried: AtomicUsize,
  }

  impl CrashTestDummy {
    /// Creates a crash test dummy design. The `id` determines order and equality of instances.
    pub(crate) fn new(id: usize) -> CrashTestDummy {
      CrashTestDummy {
        id,
        cloned: AtomicUsize::new(0),
        dropped: AtomicUsize::new(0),
        queried: AtomicUsize::new(0),
      }
    }

    /// Creates an instance of a crash test dummy that records what events it experiences
    /// and optionally panics.
    pub(crate) fn spawn(&self, panic: Panic) -> Instance<'_> {
      Instance {
        origin: self,
        panic,
      }
    }

    /// Returns how many times instances of the dummy have been cloned.
    #[allow(unused)]
    pub(crate) fn cloned(&self) -> usize {
      self.cloned.load(SeqCst)
    }

    /// Returns how many times instances of the dummy have been dropped.
    pub(crate) fn dropped(&self) -> usize {
      self.dropped.load(SeqCst)
    }

    /// Returns how many times instances of the dummy have had their `query` member invoked.
    #[allow(unused)]
    pub(crate) fn queried(&self) -> usize {
      self.queried.load(SeqCst)
    }
  }
  #[derive(Debug)]
  pub(crate) struct Instance<'a> {
    origin: &'a CrashTestDummy,
    panic: Panic,
  }

  #[derive(Copy, Clone, Debug, PartialEq, Eq)]
  pub(crate) enum Panic {
    Never,
    InClone,
    InDrop,
    InQuery,
  }

  impl Instance<'_> {
    pub(crate) fn id(&self) -> usize {
      self.origin.id
    }

    /// Some anonymous query, the result of which is already given.
    #[allow(unused)]
    pub(crate) fn query<R>(&self, result: R) -> R {
      self.origin.queried.fetch_add(1, SeqCst);
      if self.panic == Panic::InQuery {
        panic!("panic in `query`");
      }
      result
    }
  }

  impl Clone for Instance<'_> {
    fn clone(&self) -> Self {
      self.origin.cloned.fetch_add(1, SeqCst);
      if self.panic == Panic::InClone {
        panic!("panic in `clone`");
      }
      Self {
        origin: self.origin,
        panic: Panic::Never,
      }
    }
  }

  impl Drop for Instance<'_> {
    fn drop(&mut self) {
      self.origin.dropped.fetch_add(1, SeqCst);
      if self.panic == Panic::InDrop {
        panic!("panic in `drop`");
      }
    }
  }

  #[allow(clippy::non_canonical_partial_ord_impl)]
  impl PartialOrd for Instance<'_> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
      self.id().partial_cmp(&other.id())
    }
  }

  impl core::cmp::Ord for Instance<'_> {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
      self.id().cmp(&other.id())
    }
  }

  impl PartialEq for Instance<'_> {
    fn eq(&self, other: &Self) -> bool {
      self.id().eq(&other.id())
    }
  }

  impl core::cmp::Eq for Instance<'_> {}

  let d0 = CrashTestDummy::new(0);
  let d1 = CrashTestDummy::new(1);
  let d2 = CrashTestDummy::new(2);
  let d3 = CrashTestDummy::new(3);
  let d4 = CrashTestDummy::new(4);
  let d5 = CrashTestDummy::new(5);
  let d6 = CrashTestDummy::new(6);
  let d7 = CrashTestDummy::new(7);
  let mut q = GenericArrayDeque::<_, U8>::new();
  q.push_back(d3.spawn(Panic::Never));
  q.push_back(d4.spawn(Panic::Never));
  q.push_back(d5.spawn(Panic::Never));
  q.push_back(d6.spawn(Panic::Never));
  q.push_back(d7.spawn(Panic::Never));
  q.push_front(d2.spawn(Panic::Never));
  q.push_front(d1.spawn(Panic::InDrop));
  q.push_front(d0.spawn(Panic::Never));

  catch_unwind(AssertUnwindSafe(|| {
    q.extract_if(.., |_| true).for_each(drop)
  }))
  .unwrap_err();

  assert_eq!(d0.dropped(), 1);
  assert_eq!(d1.dropped(), 1);
  assert_eq!(d2.dropped(), 0);
  assert_eq!(d3.dropped(), 0);
  assert_eq!(d4.dropped(), 0);
  assert_eq!(d5.dropped(), 0);
  assert_eq!(d6.dropped(), 0);
  assert_eq!(d7.dropped(), 0);
  drop(q);
  assert_eq!(d2.dropped(), 1);
  assert_eq!(d3.dropped(), 1);
  assert_eq!(d4.dropped(), 1);
  assert_eq!(d5.dropped(), 1);
  assert_eq!(d6.dropped(), 1);
  assert_eq!(d7.dropped(), 1);
}

#[cfg(all(feature = "std", feature = "unstable"))]
#[test]
#[cfg_attr(not(panic = "unwind"), ignore = "test requires unwinding support")]
fn extract_if_pred_panic_leak() {
  use std::panic::{catch_unwind, AssertUnwindSafe};
  struct_with_counted_drop!(D(u32), DROPS);

  let mut q = GenericArrayDeque::<D, U8>::new();
  q.push_back(D(3));
  q.push_back(D(4));
  q.push_back(D(5));
  q.push_back(D(6));
  q.push_back(D(7));
  q.push_front(D(2));
  q.push_front(D(1));
  q.push_front(D(0));

  _ = catch_unwind(AssertUnwindSafe(|| {
    q.extract_if(.., |item| if item.0 >= 2 { panic!() } else { true })
      .for_each(drop)
  }));

  assert_eq!(DROPS.get(), 2); // 0 and 1
  assert_eq!(q.len(), 6);
}
