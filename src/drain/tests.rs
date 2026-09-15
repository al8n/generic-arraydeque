use crate::{typenum::U8, GenericArrayDeque};
use core::sync::atomic::{AtomicUsize, Ordering};

static DROP_COUNTER: AtomicUsize = AtomicUsize::new(0);

#[derive(Debug)]
struct DropSpy;

impl Drop for DropSpy {
  fn drop(&mut self) {
    DROP_COUNTER.fetch_add(1, Ordering::SeqCst);
  }
}

#[test]
fn drain_removes_requested_range() {
  let mut deque = GenericArrayDeque::<_, U8>::new();
  for value in 0..6 {
    assert!(deque.push_back(value).is_none());
  }

  let mut drained = [0; 2];
  let mut idx = 0;
  for value in deque.drain(2..4) {
    drained[idx] = value;
    idx += 1;
  }
  assert_eq!(&drained[..idx], &[2, 3]);
  assert_eq!(deque.len(), 4);
  assert_eq!(deque[0], 0);
  assert_eq!(deque[1], 1);
  assert_eq!(deque[2], 4);
  assert_eq!(deque[3], 5);
}

#[test]
fn drain_iterator_supports_double_ended_iteration() {
  let mut deque = GenericArrayDeque::<_, U8>::new();
  for value in 0..5 {
    assert!(deque.push_back(value).is_none());
  }

  let mut drain = deque.drain(1..4);
  assert_eq!(drain.next_back(), Some(3));
  assert_eq!(drain.next(), Some(1));
  assert_eq!(drain.next(), Some(2));
  assert_eq!(drain.next(), None);
  drop(drain);
  assert_eq!(deque.len(), 2);
  assert_eq!(deque[0], 0);
  assert_eq!(deque[1], 4);
}

#[test]
fn dropping_drain_drops_remaining_elements() {
  DROP_COUNTER.store(0, Ordering::SeqCst);
  {
    let mut deque = GenericArrayDeque::<_, U8>::new();
    for _ in 0..4 {
      assert!(deque.push_back(DropSpy).is_none());
    }
    let _ = deque.drain(1..3);
    assert_eq!(deque.len(), 2);
  }
  assert_eq!(DROP_COUNTER.load(Ordering::SeqCst), 4);
}
