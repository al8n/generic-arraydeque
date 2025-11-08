use core::iter::FusedIterator;
use core::{fmt, mem, slice};

/// An iterator over the elements of a `VecDeque`.
///
/// This `struct` is created by the [`iter`] method on [`super::VecDeque`]. See its
/// documentation for more.
///
/// [`iter`]: super::VecDeque::iter
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
  /// This has the same lifetime as the original `VecDeque`, and so the
  /// iterator can continue to be used while this exists.
  ///
  /// # Examples
  ///
  /// ```
  /// #![feature(vec_deque_iter_as_slices)]
  ///
  /// use std::collections::VecDeque;
  ///
  /// let mut deque = VecDeque::new();
  /// deque.push_back(0);
  /// deque.push_back(1);
  /// deque.push_back(2);
  /// deque.push_front(10);
  /// deque.push_front(9);
  /// deque.push_front(8);
  ///
  /// let mut iter = deque.iter();
  /// iter.next();
  /// iter.next_back();
  ///
  /// assert_eq!(iter.as_slices(), (&[9, 10][..], &[0, 1][..]));
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

impl<T> Default for Iter<'_, T> {
  /// Creates an empty `vec_deque::Iter`.
  ///
  /// ```
  /// # use std::collections::vec_deque;
  /// let iter: vec_deque::Iter<'_, u8> = Default::default();
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
