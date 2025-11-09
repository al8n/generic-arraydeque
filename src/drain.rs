use core::{
  fmt,
  iter::FusedIterator,
  marker::PhantomData,
  mem::{self, size_of},
  ops::{Range, RangeBounds},
  ptr::{self, NonNull},
};

use super::{ArrayLength, GenericArrayDeque};

impl<T, N: ArrayLength> GenericArrayDeque<T, N> {
  /// Removes the specified range from the deque in bulk, returning all
  /// removed elements as an iterator. If the iterator is dropped before
  /// being fully consumed, it drops the remaining removed elements.
  ///
  /// The returned iterator keeps a mutable borrow on the queue to optimize
  /// its implementation.
  ///
  ///
  /// # Panics
  ///
  /// Panics if the range has `start_bound > end_bound`, or, if the range is
  /// bounded on either end and past the length of the deque.
  ///
  /// # Leaking
  ///
  /// If the returned iterator goes out of scope without being dropped (due to
  /// [`mem::forget`], for example), the deque may have lost and leaked
  /// elements arbitrarily, including elements outside the range.
  ///
  /// # Examples
  ///
  /// ```
  /// use std::collections::VecDeque;
  ///
  /// let mut deque: VecDeque<_> = [1, 2, 3].into();
  /// let drained = deque.drain(2..).collect::<VecDeque<_>>();
  /// assert_eq!(drained, [3]);
  /// assert_eq!(deque, [1, 2]);
  ///
  /// // A full range clears all contents, like `clear()` does
  /// deque.drain(..);
  /// assert!(deque.is_empty());
  /// ```
  #[inline]
  pub fn drain<R>(&mut self, range: R) -> Drain<'_, T, N>
  where
    R: RangeBounds<usize>,
  {
    // Memory safety
    //
    // When the Drain is first created, the source deque is shortened to
    // make sure no uninitialized or moved-from elements are accessible at
    // all if the Drain's destructor never gets to run.
    //
    // Drain will ptr::read out the values to remove.
    // When finished, the remaining data will be copied back to cover the hole,
    // and the head/tail values will be restored correctly.
    //
    let Range { start, end } = super::range(range, ..self.len);
    let drain_start = start;
    let drain_len = end - start;

    // The deque's elements are parted into three segments:
    // * 0  -> drain_start
    // * drain_start -> drain_start+drain_len
    // * drain_start+drain_len -> self.len
    //
    // H = self.head; T = self.head+self.len; t = drain_start+drain_len; h = drain_head
    //
    // We store drain_start as self.len, and drain_len and self.len as
    // drain_len and orig_len respectively on the Drain. This also
    // truncates the effective array such that if the Drain is leaked, we
    // have forgotten about the potentially moved values after the start of
    // the drain.
    //
    //        H   h   t   T
    // [. . . o o x x o o . . .]
    //
    // "forget" about the values after the start of the drain until after
    // the drain is complete and the Drain destructor is run.

    unsafe { Drain::new(self, drain_start, drain_len) }
  }
}

/// A draining iterator over the elements of a `VecDeque`.
///
/// This `struct` is created by the [`drain`] method on [`VecDeque`]. See its
/// documentation for more.
///
/// [`drain`]: VecDeque::drain
pub struct Drain<'a, T, N: ArrayLength> {
  // We can't just use a &mut VecDeque<T, N>, as that would make Drain invariant over T
  // and we want it to be covariant instead
  deque: NonNull<GenericArrayDeque<T, N>>,
  // drain_start is stored in deque.len
  drain_len: usize,
  // index into the logical array, not the physical one (always lies in [0..deque.len))
  idx: usize,
  // number of elements remaining after dropping the drain
  new_len: usize,
  remaining: usize,
  // Needed to make Drain covariant over T
  _marker: PhantomData<&'a T>,
}

impl<'a, T, N: ArrayLength> Drain<'a, T, N> {
  pub(super) unsafe fn new(
    deque: &'a mut GenericArrayDeque<T, N>,
    drain_start: usize,
    drain_len: usize,
  ) -> Self {
    let orig_len = mem::replace(&mut deque.len, drain_start);
    let new_len = orig_len - drain_len;
    Drain {
      deque: NonNull::from(deque),
      drain_len,
      idx: drain_start,
      new_len,
      remaining: drain_len,
      _marker: PhantomData,
    }
  }

  // Only returns pointers to the slices, as that's all we need
  // to drop them. May only be called if `self.remaining != 0`.
  unsafe fn as_slices(&mut self) -> (*mut [T], *mut [T]) {
    unsafe {
      let deque = self.deque.as_mut();

      // We know that `self.idx + self.remaining <= deque.len <= usize::MAX`, so this won't overflow.
      let logical_remaining_range = self.idx..self.idx + self.remaining;

      // SAFETY: `logical_remaining_range` represents the
      // range into the logical buffer of elements that
      // haven't been drained yet, so they're all initialized,
      // and `slice::range(start..end, end) == start..end`,
      // so the preconditions for `slice_ranges` are met.
      let (a_range, b_range) =
        deque.slice_ranges(logical_remaining_range.clone(), logical_remaining_range.end);
      (
        deque.buffer_range_mut(a_range),
        deque.buffer_range_mut(b_range),
      )
    }
  }
}

impl<T: fmt::Debug, N: ArrayLength> fmt::Debug for Drain<'_, T, N> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.debug_tuple("Drain")
      .field(&self.drain_len)
      .field(&self.idx)
      .field(&self.new_len)
      .field(&self.remaining)
      .finish()
  }
}

unsafe impl<T: Sync, N: ArrayLength + Sync> Sync for Drain<'_, T, N> {}
unsafe impl<T: Send, N: ArrayLength + Send> Send for Drain<'_, T, N> {}

impl<T, N: ArrayLength> Drop for Drain<'_, T, N> {
  fn drop(&mut self) {
    struct DropGuard<'r, 'a, T, N: ArrayLength>(&'r mut Drain<'a, T, N>);

    let guard = DropGuard(self);

    if mem::needs_drop::<T>() && guard.0.remaining != 0 {
      unsafe {
        // SAFETY: We just checked that `self.remaining != 0`.
        let (front, back) = guard.0.as_slices();
        // since idx is a logical index, we don't need to worry about wrapping.
        guard.0.idx += PtrLen::len(front);
        guard.0.remaining -= PtrLen::len(front);

        ptr::drop_in_place(front);
        guard.0.remaining = 0;
        ptr::drop_in_place(back);
      }
    }

    // Dropping `guard` handles moving the remaining elements into place.
    impl<T, N: ArrayLength> Drop for DropGuard<'_, '_, T, N> {
      #[inline]
      fn drop(&mut self) {
        if mem::needs_drop::<T>() && self.0.remaining != 0 {
          unsafe {
            // SAFETY: We just checked that `self.remaining != 0`.
            let (front, back) = self.0.as_slices();
            ptr::drop_in_place(front);
            ptr::drop_in_place(back);
          }
        }

        let source_deque = unsafe { self.0.deque.as_mut() };

        let drain_len = self.0.drain_len;
        let new_len = self.0.new_len;

        if size_of::<T>() == 0 {
          // no need to copy around any memory if T is a ZST
          source_deque.len = new_len;
          return;
        }

        let head_len = source_deque.len; // #elements in front of the drain
        let tail_len = new_len - head_len; // #elements behind the drain

        // Next, we will fill the hole left by the drain with as few writes as possible.
        // The code below handles the following control flow and reduces the amount of
        // branches under the assumption that `head_len == 0 || tail_len == 0`, i.e.
        // draining at the front or at the back of the dequeue is especially common.
        //
        // H = "head index" = `deque.head`
        // h = elements in front of the drain
        // d = elements in the drain
        // t = elements behind the drain
        //
        // Note that the buffer may wrap at any point and the wrapping is handled by
        // `wrap_copy` and `to_physical_idx`.
        //
        // Case 1: if `head_len == 0 && tail_len == 0`
        // Everything was drained, reset the head index back to 0.
        //             H
        // [ . . . . . d d d d . . . . . ]
        //   H
        // [ . . . . . . . . . . . . . . ]
        //
        // Case 2: else if `tail_len == 0`
        // Don't move data or the head index.
        //         H
        // [ . . . h h h h d d d d . . . ]
        //         H
        // [ . . . h h h h . . . . . . . ]
        //
        // Case 3: else if `head_len == 0`
        // Don't move data, but move the head index.
        //         H
        // [ . . . d d d d t t t t . . . ]
        //                 H
        // [ . . . . . . . t t t t . . . ]
        //
        // Case 4: else if `tail_len <= head_len`
        // Move data, but not the head index.
        //       H
        // [ . . h h h h d d d d t t . . ]
        //       H
        // [ . . h h h h t t . . . . . . ]
        //
        // Case 5: else
        // Move data and the head index.
        //       H
        // [ . . h h d d d d t t t t . . ]
        //               H
        // [ . . . . . . h h t t t t . . ]

        // When draining at the front (`.drain(..n)`) or at the back (`.drain(n..)`),
        // we don't need to copy any data. The number of elements copied would be 0.
        if head_len != 0 && tail_len != 0 {
          join_head_and_tail_wrapping(source_deque, drain_len, head_len, tail_len);
          // Marking this function as cold helps LLVM to eliminate it entirely if
          // this branch is never taken.
          // We use `#[cold]` instead of `#[inline(never)]`, because inlining this
          // function into the general case (`.drain(n..m)`) is fine.
          // See `tests/codegen-llvm/vecdeque-drain.rs` for a test.
          #[cold]
          fn join_head_and_tail_wrapping<T, N: ArrayLength>(
            source_deque: &mut GenericArrayDeque<T, N>,
            drain_len: usize,
            head_len: usize,
            tail_len: usize,
          ) {
            // Pick whether to move the head or the tail here.
            let (src, dst, len);
            if head_len < tail_len {
              src = source_deque.head;
              dst = source_deque.to_physical_idx(drain_len);
              len = head_len;
            } else {
              src = source_deque.to_physical_idx(head_len + drain_len);
              dst = source_deque.to_physical_idx(head_len);
              len = tail_len;
            };

            unsafe {
              source_deque.wrap_copy(src, dst, len);
            }
          }
        }

        if new_len == 0 {
          // Special case: If the entire dequeue was drained, reset the head back to 0,
          // like `.clear()` does.
          source_deque.head = 0;
        } else if head_len < tail_len {
          // If we moved the head above, then we need to adjust the head index here.
          source_deque.head = source_deque.to_physical_idx(drain_len);
        }
        source_deque.len = new_len;
      }
    }
  }
}

impl<T, N: ArrayLength> Iterator for Drain<'_, T, N> {
  type Item = T;

  #[inline]
  fn next(&mut self) -> Option<T> {
    if self.remaining == 0 {
      return None;
    }
    let wrapped_idx = unsafe { self.deque.as_ref().to_physical_idx(self.idx) };
    self.idx += 1;
    self.remaining -= 1;
    Some(unsafe { self.deque.as_mut().buffer_read(wrapped_idx) })
  }

  #[inline]
  fn size_hint(&self) -> (usize, Option<usize>) {
    let len = self.remaining;
    (len, Some(len))
  }
}

impl<T, N: ArrayLength> DoubleEndedIterator for Drain<'_, T, N> {
  #[inline]
  fn next_back(&mut self) -> Option<T> {
    if self.remaining == 0 {
      return None;
    }
    self.remaining -= 1;
    let wrapped_idx = unsafe {
      self
        .deque
        .as_ref()
        .to_physical_idx(self.idx + self.remaining)
    };
    Some(unsafe { self.deque.as_mut().buffer_read(wrapped_idx) })
  }
}

impl<T, N: ArrayLength> ExactSizeIterator for Drain<'_, T, N> {}

impl<T, N: ArrayLength> FusedIterator for Drain<'_, T, N> {}

trait PtrLen {
  #[allow(unstable_name_collisions)]
  /// # Safety
  /// - The pointer must be initialized and valid for reads.
  unsafe fn len(self) -> usize;
}

#[rustversion::since(1.79)]
impl<T> PtrLen for *mut [T] {
  #[allow(unstable_name_collisions)]
  #[cfg_attr(not(tarpaulin), inline(always))]
  unsafe fn len(self) -> usize {
    <*mut [T]>::len(self)
  }
}

#[rustversion::before(1.79)]
impl<T> PtrLen for *mut [T] {
  #[allow(unstable_name_collisions)]
  #[cfg_attr(not(tarpaulin), inline(always))]
  unsafe fn len(self) -> usize {
    (&*self).len()
  }
}

#[cfg(test)]
mod tests {
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
}
