use core::{
  fmt,
  ops::{Range, RangeBounds},
  ptr,
};

use super::{ArrayLength, GenericArrayDeque};

impl<T, N> GenericArrayDeque<T, N>
where
  N: ArrayLength,
{
  /// Creates an iterator which uses a closure to determine if an element in the range should be removed.
  ///
  /// If the closure returns `true`, the element is removed from the deque and yielded. If the closure
  /// returns `false`, or panics, the element remains in the deque and will not be yielded.
  ///
  /// Only elements that fall in the provided range are considered for extraction, but any elements
  /// after the range will still have to be moved if any element has been extracted.
  ///
  /// If the returned `ExtractIf` is not exhausted, e.g. because it is dropped without iterating
  /// or the iteration short-circuits, then the remaining elements will be retained.
  /// Use [`retain_mut`] with a negated predicate if you do not need the returned iterator.
  ///
  /// [`retain_mut`]: GenericArrayDeque::retain_mut
  ///
  /// Using this method is equivalent to the following code:
  ///
  /// ```
  /// # ![cfg(feature = "std")])]
  /// # use generic_arraydeque::{GenericArrayDeque, typenum::U10};
  /// # let some_predicate = |x: &mut i32| { *x % 2 == 1 };
  /// # let mut deq: GenericArrayDeque<_, U10> = (0..10).collect();
  /// # let mut deq2 = deq.clone();
  /// # let range = 1..5;
  /// let mut i = range.start;
  /// let end_items = deq.len() - range.end;
  /// # let mut extracted = vec![];
  ///
  /// while i < deq.len() - end_items {
  ///     if some_predicate(&mut deq[i]) {
  ///         let val = deq.remove(i).unwrap();
  ///         // your code here
  /// #         extracted.push(val);
  ///     } else {
  ///         i += 1;
  ///     }
  /// }
  ///
  /// # let extracted2: Vec<_> = deq2.extract_if(range, some_predicate).collect();
  /// # assert_eq!(deq, deq2);
  /// # assert_eq!(extracted, extracted2);
  /// ```
  ///
  /// But `extract_if` is easier to use. `extract_if` is also more efficient,
  /// because it can backshift the elements of the array in bulk.
  ///
  /// The iterator also lets you mutate the value of each element in the
  /// closure, regardless of whether you choose to keep or remove it.
  ///
  /// # Panics
  ///
  /// If `range` is out of bounds.
  ///
  /// # Examples
  ///
  /// Splitting a deque into even and odd values, reusing the original deque:
  ///
  /// ```
  /// use generic_arraydeque::{GenericArrayDeque, typenum::U10};
  ///
  /// let mut numbers = GenericArrayDeque::from([1, 2, 3, 4, 5, 6, 8, 9, 11, 13, 14, 15]);
  ///
  /// let evens = numbers.extract_if(.., |x| *x % 2 == 0).collect::<GenericArrayDeque<_>>();
  /// let odds = numbers;
  ///
  /// assert_eq!(evens, GenericArrayDeque::from([2, 4, 6, 8, 14]));
  /// assert_eq!(odds, GenericArrayDeque::from([1, 3, 5, 9, 11, 13, 15]));
  /// ```
  ///
  /// Using the range argument to only process a part of the deque:
  ///
  /// ```
  /// use generic_arraydeque::{GenericArrayDeque, typenum::U10};
  ///
  /// let mut items = GenericArrayDeque::from([0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 2, 1, 2]);
  /// let ones = items.extract_if(7.., |x| *x == 1).collect::<GenericArrayDeque<_>>();
  /// assert_eq!(items, GenericArrayDeque::from([0, 0, 0, 0, 0, 0, 0, 2, 2, 2]));
  /// assert_eq!(ones.len(), 3);
  /// ```
  pub fn extract_if<F, R>(&mut self, range: R, filter: F) -> ExtractIf<'_, T, F, N>
  where
    F: FnMut(&mut T) -> bool,
    R: RangeBounds<usize>,
  {
    ExtractIf::new(self, filter, range)
  }
}

/// An iterator which uses a closure to determine if an element should be removed.
///
/// This struct is created by [`GenericArrayDeque::extract_if`].
/// See its documentation for more.
///
/// # Example
///
/// ```
/// use generic_arraydeque::{ExtractIf, GenericArrayDeque, typenum::U3};
///
/// let mut v = GenericArrayDeque::<_, U3>::try_from_array([0, 1, 2]);
/// let iter: ExtractIf<'_, _, _> = v.extract_if(.., |x| *x % 2 == 0);
/// ```
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct ExtractIf<'a, T, F, N: ArrayLength> {
  vec: &'a mut GenericArrayDeque<T, N>,
  /// The index of the item that will be inspected by the next call to `next`.
  idx: usize,
  /// Elements at and beyond this point will be retained. Must be equal or smaller than `old_len`.
  end: usize,
  /// The number of items that have been drained (removed) thus far.
  del: usize,
  /// The original length of `vec` prior to draining.
  old_len: usize,
  /// The filter test predicate.
  pred: F,
}

impl<'a, T, F, N: ArrayLength> ExtractIf<'a, T, F, N> {
  pub(super) fn new<R: RangeBounds<usize>>(
    vec: &'a mut GenericArrayDeque<T, N>,
    pred: F,
    range: R,
  ) -> Self {
    let old_len = vec.len();
    let Range { start, end } = super::range(range, ..old_len);

    // Guard against the deque getting leaked (leak amplification)
    vec.len = 0;
    ExtractIf {
      vec,
      idx: start,
      del: 0,
      end,
      old_len,
      pred,
    }
  }
}

impl<T, F, N: ArrayLength> Iterator for ExtractIf<'_, T, F, N>
where
  F: FnMut(&mut T) -> bool,
{
  type Item = T;

  fn next(&mut self) -> Option<T> {
    while self.idx < self.end {
      let i = self.idx;
      // SAFETY:
      //  We know that `i < self.end` from the if guard and that `self.end <= self.old_len` from
      //  the validity of `Self`. Therefore `i` points to an element within `vec`.
      //
      //  Additionally, the i-th element is valid because each element is visited at most once
      //  and it is the first time we access vec[i].
      //
      //  Note: we can't use `vec.get_mut(i).unwrap()` here since the precondition for that
      //  function is that i < vec.len, but we've set vec's length to zero.
      let idx = self.vec.to_physical_idx(i);
      let cur = unsafe { (&mut *self.vec.ptr_mut().add(idx)).assume_init_mut() };
      let drained = (self.pred)(cur);
      // Update the index *after* the predicate is called. If the index
      // is updated prior and the predicate panics, the element at this
      // index would be leaked.
      self.idx += 1;
      if drained {
        self.del += 1;
        // SAFETY: We never touch this element again after returning it.
        return Some(unsafe { ptr::read(cur) });
      } else if self.del > 0 {
        let hole_slot = self.vec.to_physical_idx(i - self.del);
        // SAFETY: `self.del` > 0, so the hole slot must not overlap with current element.
        // We use copy for move, and never touch this element again.
        unsafe { self.vec.wrap_copy(idx, hole_slot, 1) };
      }
    }
    None
  }

  fn size_hint(&self) -> (usize, Option<usize>) {
    (0, Some(self.end - self.idx))
  }
}

impl<T, F, N: ArrayLength> Drop for ExtractIf<'_, T, F, N> {
  fn drop(&mut self) {
    if self.del > 0 {
      let src = self.vec.to_physical_idx(self.idx);
      let dst = self.vec.to_physical_idx(self.idx - self.del);
      let len = self.old_len - self.idx;
      // SAFETY: Trailing unchecked items must be valid since we never touch them.
      unsafe { self.vec.wrap_copy(src, dst, len) };
    }
    self.vec.len = self.old_len - self.del;
  }
}

impl<T, F, N> fmt::Debug for ExtractIf<'_, T, F, N>
where
  T: fmt::Debug,
  N: ArrayLength,
{
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let peek = if self.idx < self.end {
      let idx = self.vec.to_physical_idx(self.idx);
      // This has to use pointer arithmetic as `self.vec[self.idx]` or
      // `self.vec.get_unchecked(self.idx)` wouldn't work since we
      // temporarily set the length of `self.vec` to zero.
      //
      // SAFETY:
      // Since `self.idx` is smaller than `self.end` and `self.end` is
      // smaller than `self.old_len`, `idx` is valid for indexing the
      // buffer. Also, per the invariant of `self.idx`, this element
      // has not been inspected/moved out yet.
      Some(unsafe { &*self.vec.ptr().add(idx) })
    } else {
      None
    };
    f.debug_struct("ExtractIf")
      .field("peek", &peek)
      .finish_non_exhaustive()
  }
}
