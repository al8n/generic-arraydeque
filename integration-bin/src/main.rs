use generic_arraydeque::{typenum::U8, GenericArrayDeque};
use std::{cell::RefCell, rc::Rc};

#[derive(Debug)]
struct DropTracker {
  id: String,
  payload: String,
  log: Rc<RefCell<Vec<String>>>,
}

impl DropTracker {
  fn new(log: &Rc<RefCell<Vec<String>>>, id: i32) -> Self {
    Self {
      id: id.to_string(),
      payload: format!("payload-{id}"),
      log: Rc::clone(log),
    }
  }
}

impl Drop for DropTracker {
  fn drop(&mut self) {
    self.log.borrow_mut().push(self.id.clone());
  }
}

fn main() {
  let drops = Rc::new(RefCell::new(Vec::new()));

  {
    let mut deque = GenericArrayDeque::<DropTracker, U8>::new();

    for id in 0..4 {
      assert!(deque.push_back(DropTracker::new(&drops, id)).is_none());
    }

    for id in 4..8 {
      assert!(deque.push_front(DropTracker::new(&drops, id)).is_none());
    }

    deque.rotate_left(3);

    for (idx, elem) in deque.range_mut(2..6).enumerate() {
      elem.payload.push_str(&format!("-range-{idx}"));
    }

    // Preserve a deterministic subset so `drain(1..)` actually removes items.
    deque.retain(|elem| elem.id.parse::<i32>().unwrap() % 2 == 0);

    let drained: Vec<_> = deque.drain(1..).collect();
    assert!(!drained.is_empty());

    drop(drained);

    let slice = deque.make_contiguous();
    slice.iter_mut().for_each(|elem| elem.payload.push_str("-contig"));
    assert!(deque.as_slices().1.is_empty());
  }

  let mut dropped = drops.borrow().clone();
  dropped.sort();
  let expected = (0..8).map(|id| id.to_string()).collect::<Vec<_>>();
  assert_eq!(dropped, expected);
}
