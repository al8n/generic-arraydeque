use super::*;
use generic_array::typenum::*;
use std::{string::{String, ToString}, vec, vec::Vec};

fn s<T: ToString>(value: T) -> String {
  value.to_string()
}

macro_rules! sarr {
  ($($val:expr),+ $(,)?) => {
    [$(s($val)),+]
  };
}

#[test]
fn heap_test_swap_front_back_remove() {
  fn run(back: bool) {
    let mut tester = GenericArrayDeque::<String, U15>::new();
    let usable_cap = tester.capacity();
    let final_len = usable_cap / 2;

    for len in 0..final_len {
      let expected: GenericArrayDeque<_, U15> = if back {
        GenericArrayDeque::try_from_exact_iter((0..len).map(s)).unwrap()
      } else {
        GenericArrayDeque::try_from_exact_iter((0..len).rev().map(s)).unwrap()
      };
      for head_pos in 0..usable_cap {
        tester.head = head_pos;
        tester.len = 0;
        if back {
          for i in 0..len * 2 {
            tester.push_front(s(i));
          }
          for i in 0..len {
            assert_eq!(tester.swap_remove_back(i), Some(s(len * 2 - 1 - i)));
          }
        } else {
          for i in 0..len * 2 {
            tester.push_back(s(i));
          }
          for i in 0..len {
            let idx = tester.len() - 1 - i;
            assert_eq!(tester.swap_remove_front(idx), Some(s(len * 2 - 1 - i)));
          }
        }
        assert!(tester.head <= tester.capacity());
        assert!(tester.len <= tester.capacity());
        assert_eq!(tester, expected);
      }
    }
  }
  run(true);
  run(false);
}

#[test]
fn heap_test_insert() {
  let mut tester = GenericArrayDeque::<String, U15>::new();
  let cap = tester.capacity();
  let minlen = if cfg!(miri) { cap - 1 } else { 1 };
  for len in minlen..cap {
    let expected = GenericArrayDeque::<String, U15>::try_from_iter((0..).take(len).map(s)).unwrap();
    for head_pos in 0..cap {
      for to_insert in 0..len {
        tester.head = head_pos;
        tester.len = 0;
        for i in 0..len {
          if i != to_insert {
            tester.push_back(s(i));
          }
        }
        tester.insert(to_insert, s(to_insert));
        assert!(tester.head <= tester.capacity());
        assert!(tester.len <= tester.capacity());
        assert_eq!(tester, expected);
      }
    }
  }
}

#[test]
fn heap_test_get_mut() {
  let mut tester = GenericArrayDeque::<String, U5>::new();
  tester.push_back(s(1));
  tester.push_back(s(2));
  tester.push_back(s(3));

  if let Some(elem) = tester.get_mut(0) {
    assert_eq!(elem, "1");
    *elem = s(10);
  }

  if let Some(elem) = tester.get_mut(2) {
    assert_eq!(elem, "3");
    *elem = s(30);
  }

  assert_eq!(tester.get(0).map(|v| v.as_str()), Some("10"));
  assert_eq!(tester.get(2).map(|v| v.as_str()), Some("30"));
  assert_eq!(tester.get_mut(3), None);

  tester.remove(2);
  assert_eq!(tester.len(), 2);
  assert_eq!(tester.get(1).map(|v| v.as_str()), Some("2"));
}

#[test]
fn heap_test_swap() {
  let mut tester = GenericArrayDeque::<String, U5>::new();
  tester.push_back(s(1));
  tester.push_back(s(2));
  tester.push_back(s(3));

  tester.swap(0, 0);
  assert_eq!(tester, sarr![1, 2, 3]);
  tester.swap(0, 1);
  assert_eq!(tester, sarr![2, 1, 3]);
  tester.swap(2, 1);
  assert_eq!(tester, sarr![2, 3, 1]);
  tester.swap(1, 2);
  assert_eq!(tester, sarr![2, 1, 3]);
  tester.swap(0, 2);
  assert_eq!(tester, sarr![3, 1, 2]);
  tester.swap(2, 2);
  assert_eq!(tester, sarr![3, 1, 2]);
}

#[test]
fn heap_test_rotate_left_right() {
  let mut tester: GenericArrayDeque<_, U10> =
    GenericArrayDeque::try_from_iter((1..=10).map(s)).unwrap();
  assert_eq!(tester.len(), 10);

  tester.rotate_left(0);
  assert_eq!(tester, sarr![1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);

  tester.rotate_right(0);
  assert_eq!(tester, sarr![1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);

  tester.rotate_left(3);
  assert_eq!(tester, sarr![4, 5, 6, 7, 8, 9, 10, 1, 2, 3]);

  tester.rotate_right(5);
  assert_eq!(tester, sarr![9, 10, 1, 2, 3, 4, 5, 6, 7, 8]);

  tester.rotate_left(tester.len());
  assert_eq!(tester, sarr![9, 10, 1, 2, 3, 4, 5, 6, 7, 8]);

  tester.rotate_right(tester.len());
  assert_eq!(tester, sarr![9, 10, 1, 2, 3, 4, 5, 6, 7, 8]);

  tester.rotate_left(1);
  assert_eq!(tester, sarr![10, 1, 2, 3, 4, 5, 6, 7, 8, 9]);
}

#[test]
fn heap_test_drain() {
  let mut tester: GenericArrayDeque<String, U7> = GenericArrayDeque::new();

  let cap = tester.capacity();
  for len in 0..=cap {
    for head in 0..cap {
      for drain_start in 0..=len {
        for drain_end in drain_start..=len {
          tester.head = head;
          tester.len = 0;
          for i in 0..len {
            tester.push_back(s(i));
          }

          let drained: GenericArrayDeque<_, U7> =
            GenericArrayDeque::try_from_iter(tester.drain(drain_start..drain_end)).unwrap();
          let drained_expected: GenericArrayDeque<_, U7> =
            GenericArrayDeque::try_from_iter((drain_start..drain_end).map(s)).unwrap();
          assert_eq!(drained, drained_expected);

          assert_eq!(tester.capacity(), cap);
          assert!(tester.head <= tester.capacity());
          assert!(tester.len <= tester.capacity());

          let expected: GenericArrayDeque<_, U14> =
            GenericArrayDeque::try_from_iter((0..drain_start).chain(drain_end..len).map(s))
              .unwrap();
          assert_eq!(expected, tester);
        }
      }
    }
  }
}

#[test]
fn heap_test_split_off() {
  let mut tester = GenericArrayDeque::<String, U15>::new();
  let cap = tester.capacity();

  let minlen = if cfg!(miri) { cap - 1 } else { 0 };
  for len in minlen..cap {
    for at in 0..=len {
      let expected_self =
        GenericArrayDeque::<String, U15>::try_from_iter((0..).take(at).map(s)).unwrap();
      let expected_other =
        GenericArrayDeque::<String, U15>::try_from_iter((at..).take(len - at).map(s)).unwrap();

      for head_pos in 0..cap {
        tester.head = head_pos;
        tester.len = 0;
        for i in 0..len {
          tester.push_back(s(i));
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
fn heap_test_from_vec() {
  let deque = GenericArrayDeque::<String, U4>::try_from_vec(
    vec!["1", "2", "3", "4"].into_iter().map(s).collect(),
  )
  .unwrap();
  assert_eq!(deque.len(), 4);

  let result =
    GenericArrayDeque::<String, U2>::try_from_vec(vec!["1", "2", "3"].into_iter().map(s).collect());
  assert!(result.is_err());
}

#[cfg(any(feature = "alloc", feature = "std"))]
#[test]
fn heap_test_extend_basic() {
  let mut deque = GenericArrayDeque::<String, U4>::new();
  deque.try_extend_from_exact_iter(["1".to_string(), "2".to_string()]);
  assert_eq!(deque.len(), 2);
  assert_eq!(deque[0], "1");
  assert_eq!(deque[1], "2");
}

#[test]
fn heap_make_contiguous_big_head() {
  let mut tester = GenericArrayDeque::<String, U15>::new();
  for i in 0..3 {
    tester.push_back(s(i));
  }
  for i in 3..10 {
    tester.push_front(s(i));
  }
  let expected_start = tester.as_slices().1.len();
  tester.make_contiguous();
  assert_eq!(tester.head, expected_start);
  let expected = sarr![9, 8, 7, 6, 5, 4, 3, 0, 1, 2];
  assert_eq!(tester.as_slices(), (&expected[..], &[][..]));
}

#[test]
fn heap_make_contiguous_big_tail() {
  let mut tester = GenericArrayDeque::<String, U15>::new();
  for i in 0..8 {
    tester.push_back(s(i));
  }
  for i in 8..10 {
    tester.push_front(s(i));
  }
  tester.make_contiguous();
  let expected = sarr![9, 8, 0, 1, 2, 3, 4, 5, 6, 7];
  assert_eq!(tester.as_slices(), (&expected[..], &[][..]));
}

#[test]
fn heap_make_contiguous_small_free() {
  let mut tester = GenericArrayDeque::<String, U16>::new();
  for ch in b'A'..b'I' {
    tester.push_back(String::from(ch as char));
  }
  for ch in b'I'..b'N' {
    tester.push_front(String::from(ch as char));
  }
  tester.make_contiguous();
  let expected = [
    "M", "L", "K", "J", "I", "A", "B", "C", "D", "E", "F", "G", "H",
  ]
  .into_iter()
  .map(s)
  .collect::<Vec<_>>();
  assert_eq!(tester.as_slices(), (&expected[..], &[][..]));

  tester.clear();
  for ch in b'I'..b'N' {
    tester.push_back(String::from(ch as char));
  }
  for ch in b'A'..b'I' {
    tester.push_front(String::from(ch as char));
  }
  tester.make_contiguous();
  let expected = [
    "H", "G", "F", "E", "D", "C", "B", "A", "I", "J", "K", "L", "M",
  ]
  .into_iter()
  .map(s)
  .collect::<Vec<_>>();
  assert_eq!(tester.as_slices(), (&expected[..], &[][..]));
}

#[test]
fn heap_make_contiguous_head_to_end() {
  let mut tester = GenericArrayDeque::<String, U16>::new();
  for ch in b'A'..b'L' {
    tester.push_back(String::from(ch as char));
  }
  for ch in b'L'..b'Q' {
    tester.push_front(String::from(ch as char));
  }
  tester.make_contiguous();
  let expected = [
    "P", "O", "N", "M", "L", "A", "B", "C", "D", "E", "F", "G", "H", "I", "J", "K",
  ]
  .into_iter()
  .map(s)
  .collect::<Vec<_>>();
  assert_eq!(tester.as_slices(), (&expected[..], &[][..]));

  tester.clear();
  for ch in b'L'..b'Q' {
    tester.push_back(String::from(ch as char));
  }
  for ch in b'A'..b'L' {
    tester.push_front(String::from(ch as char));
  }
  tester.make_contiguous();
  let expected = [
    "K", "J", "I", "H", "G", "F", "E", "D", "C", "B", "A", "L", "M", "N", "O", "P",
  ]
  .into_iter()
  .map(s)
  .collect::<Vec<_>>();
  assert_eq!(tester.as_slices(), (&expected[..], &[][..]));
}

#[cfg(any(feature = "alloc", feature = "std"))]
#[test]
fn heap_make_contiguous_head_to_end_2() {
  let mut dq = GenericArrayDeque::<String, U6>::try_from_iter((0..6).map(s)).unwrap();
  dq.pop_front();
  dq.pop_front();
  dq.push_back(s(6));
  dq.push_back(s(7));
  dq.push_back(s(8));
  dq.make_contiguous();
  let collected: Vec<_> = dq.iter().cloned().collect();
  assert_eq!(dq.as_slices(), (&collected[..], &[][..]));
}
