use core::iter::FusedIterator;
use core::{fmt, mem, slice};

/// A mutable iterator over the elements of a `VecDeque`.
///
/// This `struct` is created by the [`iter_mut`] method on [`super::VecDeque`]. See its
/// documentation for more.
///
/// [`iter_mut`]: super::VecDeque::iter_mut
pub struct IterMut<'a, T> {
  i1: slice::IterMut<'a, T>,
  i2: slice::IterMut<'a, T>,
}

impl<'a, T> IterMut<'a, T> {
  pub(super) fn new(i1: slice::IterMut<'a, T>, i2: slice::IterMut<'a, T>) -> Self {
    Self { i1, i2 }
  }

  /// Views the underlying data as a pair of subslices of the original data.
  ///
  /// The slices contain, in order, the contents of the deque not yet yielded
  /// by the iterator.
  ///
  /// To avoid creating `&mut` references that alias, this is forced to
  /// consume the iterator.
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
  /// let mut iter = deque.iter_mut();
  /// iter.next();
  /// iter.next_back();
  ///
  /// let slices = iter.into_slices();
  /// slices.0[0] = 42;
  /// slices.1[0] = 24;
  /// assert_eq!(deque.as_slices(), (&[8, 42, 10][..], &[24, 1, 2][..]));
  /// ```
  pub fn into_slices(self) -> (&'a mut [T], &'a mut [T]) {
    (self.i1.into_slice(), self.i2.into_slice())
  }

  /// Views the underlying data as a pair of subslices of the original data.
  ///
  /// The slices contain, in order, the contents of the deque not yet yielded
  /// by the iterator.
  ///
  /// To avoid creating `&mut [T]` references that alias, the returned slices
  /// borrow their lifetimes from the iterator the method is applied on.
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
  /// let mut iter = deque.iter_mut();
  /// iter.next();
  /// iter.next_back();
  ///
  /// assert_eq!(iter.as_slices(), (&[9, 10][..], &[0, 1][..]));
  /// ```
  pub fn as_slices(&self) -> (&[T], &[T]) {
    (self.i1.as_slice(), self.i2.as_slice())
  }
}

impl<T: fmt::Debug> fmt::Debug for IterMut<'_, T> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.debug_tuple("IterMut")
      .field(&self.i1.as_slice())
      .field(&self.i2.as_slice())
      .finish()
  }
}

impl<T> Default for IterMut<'_, T> {
  /// Creates an empty `vec_deque::IterMut`.
  ///
  /// ```
  /// # use std::collections::vec_deque;
  /// let iter: vec_deque::IterMut<'_, u8> = Default::default();
  /// assert_eq!(iter.len(), 0);
  /// ```
  fn default() -> Self {
    IterMut {
      i1: Default::default(),
      i2: Default::default(),
    }
  }
}

impl<'a, T> Iterator for IterMut<'a, T> {
  type Item = &'a mut T;

  #[inline]
  fn next(&mut self) -> Option<&'a mut T> {
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
  fn last(mut self) -> Option<&'a mut T> {
    self.next_back()
  }
}

impl<'a, T> DoubleEndedIterator for IterMut<'a, T> {
  #[inline]
  fn next_back(&mut self) -> Option<&'a mut T> {
    match self.i2.next_back() {
      Some(val) => Some(val),
      None => {
        // most of the time, the iterator will either always
        // call next(), or always call next_back(). By swapping
        // the iterators once the first one is empty, we ensure
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

impl<T> ExactSizeIterator for IterMut<'_, T> {
  fn len(&self) -> usize {
    self.i1.len() + self.i2.len()
  }
}

impl<T> FusedIterator for IterMut<'_, T> {}
