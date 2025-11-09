use core::{fmt, iter::FusedIterator, mem, slice};

/// An iterator over the elements of a [`GenericArrayDeque`](crate::GenericArrayDeque).
///
/// This `struct` is created by the [`iter`] method on [`super::GenericArrayDeque`]. See its
/// documentation for more.
///
/// [`iter`]: super::GenericArrayDeque::iter
#[derive(Clone)]
pub struct Iter<'a, T> {
  i1: slice::Iter<'a, T>,
  i2: slice::Iter<'a, T>,
}

impl<'a, T> Iter<'a, T> {
  pub(super) const fn new(i1: slice::Iter<'a, T>, i2: slice::Iter<'a, T>) -> Self {
    Self { i1, i2 }
  }

  /// Views the underlying data as a pair of subslices of the original data.
  ///
  /// The slices contain, in order, the contents of the deque not yet yielded
  /// by the iterator.
  ///
  /// This has the same lifetime as the original deque, and so the
  /// iterator can continue to be used while this exists.
  ///
  /// # Examples
  ///
  /// ```
  /// use generic_arraydeque::{GenericArrayDeque, typenum::U4};
  ///
  /// let mut deque = GenericArrayDeque::<u32, U4>::new();
  /// for value in 0..3 {
  ///     assert!(deque.push_back(value).is_none());
  /// }
  ///
  /// let mut iter = deque.iter();
  /// assert_eq!(iter.next(), Some(&0));
  /// let (front, back) = iter.as_slices();
  /// assert_eq!(front, &[1, 2]);
  /// assert!(back.is_empty());
  /// ```
  pub fn as_slices(&self) -> (&'a [T], &'a [T]) {
    (self.i1.as_slice(), self.i2.as_slice())
  }
}

impl<T: fmt::Debug> fmt::Debug for Iter<'_, T> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.debug_tuple("Iter")
      .field(&self.i1.as_slice())
      .field(&self.i2.as_slice())
      .finish()
  }
}

#[rustversion::since(1.70)]
impl<T> Default for Iter<'_, T> {
  /// Creates an empty iterator.
  ///
  /// ```
  /// use generic_arraydeque::Iter;
  ///
  /// let iter: Iter<'_, u8> = Default::default();
  /// assert_eq!(iter.len(), 0);
  /// ```
  fn default() -> Self {
    Iter {
      i1: Default::default(),
      i2: Default::default(),
    }
  }
}

impl<'a, T> Iterator for Iter<'a, T> {
  type Item = &'a T;

  #[inline]
  fn next(&mut self) -> Option<&'a T> {
    match self.i1.next() {
      Some(val) => Some(val),
      None => {
        // most of the time, the iterator will either always
        // call next(), or always call next_back(). By swapping
        // the iterators once the first one is empty, we ensure
        // that the first branch is taken as often as possible,
        // without sacrificing correctness, as i1 is empty anyways
        mem::swap(&mut self.i1, &mut self.i2);
        self.i1.next()
      }
    }
  }

  #[inline]
  fn size_hint(&self) -> (usize, Option<usize>) {
    let len = self.len();
    (len, Some(len))
  }

  fn fold<Acc, F>(self, accum: Acc, mut f: F) -> Acc
  where
    F: FnMut(Acc, Self::Item) -> Acc,
  {
    let accum = self.i1.fold(accum, &mut f);
    self.i2.fold(accum, &mut f)
  }

  #[inline]
  fn last(mut self) -> Option<&'a T> {
    self.next_back()
  }
}

impl<'a, T> DoubleEndedIterator for Iter<'a, T> {
  #[inline]
  fn next_back(&mut self) -> Option<&'a T> {
    match self.i2.next_back() {
      Some(val) => Some(val),
      None => {
        // most of the time, the iterator will either always
        // call next(), or always call next_back(). By swapping
        // the iterators once the second one is empty, we ensure
        // that the first branch is taken as often as possible,
        // without sacrificing correctness, as i2 is empty anyways
        mem::swap(&mut self.i1, &mut self.i2);
        self.i2.next_back()
      }
    }
  }

  fn rfold<Acc, F>(self, accum: Acc, mut f: F) -> Acc
  where
    F: FnMut(Acc, Self::Item) -> Acc,
  {
    let accum = self.i2.rfold(accum, &mut f);
    self.i1.rfold(accum, &mut f)
  }
}

impl<T> ExactSizeIterator for Iter<'_, T> {
  fn len(&self) -> usize {
    self.i1.len() + self.i2.len()
  }
}

impl<T> FusedIterator for Iter<'_, T> {}

#[cfg(test)]
mod tests {
  use crate::{typenum::U4, GenericArrayDeque};

  #[test]
  fn as_slices_reflect_wrapping_layout() {
    let mut deque = GenericArrayDeque::<_, U4>::new();
    for value in 0..4 {
      assert!(deque.push_back(value).is_none());
    }
    assert_eq!(deque.pop_front(), Some(0));
    assert!(deque.push_back(4).is_none());

    let mut iter = deque.iter();
    assert_eq!(iter.next(), Some(&1));
    let (front, back) = iter.as_slices();
    assert_eq!(front, &[2, 3]);
    assert_eq!(back, &[4]);
  }

  #[test]
  fn next_and_next_back_cover_all_elements() {
    let mut deque = GenericArrayDeque::<_, U4>::new();
    for value in 0..4 {
      assert!(deque.push_back(value).is_none());
    }

    let mut iter = deque.iter();
    assert_eq!(iter.next(), Some(&0));
    assert_eq!(iter.next_back(), Some(&3));
    assert_eq!(iter.len(), 2);
    assert_eq!(iter.next(), Some(&1));
    assert_eq!(iter.next_back(), Some(&2));
    assert_eq!(iter.next(), None);
    assert_eq!(iter.next_back(), None);
  }

  #[allow(clippy::unnecessary_fold)]
  #[test]
  fn fold_and_rfold_process_all_items() {
    let mut deque = GenericArrayDeque::<_, U4>::new();
    for value in 0..4 {
      assert!(deque.push_back(value).is_none());
    }
    let iter = deque.iter();
    let sum = iter.clone().fold(0, |acc, &value| acc + value);
    assert_eq!(sum, 6);
    let rsum = iter.rfold(0, |acc, &value| acc + value);
    assert_eq!(rsum, 6);
  }

  #[test]
  fn size_hint_tracks_remaining_items() {
    let mut deque = GenericArrayDeque::<_, U4>::new();
    for value in 0..4 {
      assert!(deque.push_back(value).is_none());
    }
    let mut iter = deque.iter();
    assert_eq!(iter.size_hint(), (4, Some(4)));
    iter.next();
    assert_eq!(iter.size_hint(), (3, Some(3)));
    iter.next_back();
    assert_eq!(iter.size_hint(), (2, Some(2)));
  }

  #[test]
  fn last_returns_final_element() {
    let mut deque = GenericArrayDeque::<_, U4>::new();
    for value in 0..4 {
      assert!(deque.push_back(value).is_none());
    }
    assert_eq!(deque.iter().last(), Some(&3));
  }

  #[rustversion::since(1.70)]
  #[test]
  fn default_is_empty() {
    use super::Iter;

    let iter: Iter<'static, u8> = Default::default();
    assert_eq!(iter.len(), 0);
    assert_eq!(iter.size_hint(), (0, Some(0)));
  }
}
