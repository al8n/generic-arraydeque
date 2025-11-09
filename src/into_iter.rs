use core::{fmt, iter::FusedIterator};

use super::{ArrayLength, GenericArrayDeque};

/// An owning iterator over the elements of a [`GenericArrayDeque`].
///
/// This `struct` is created by the [`into_iter`] method on [`GenericArrayDeque`]
/// (provided by the [`IntoIterator`] trait). See its documentation for more.
///
/// [`GenericArrayDeque`]: crate::GenericArrayDeque
/// [`into_iter`]: GenericArrayDeque::into_iter
#[derive(Clone)]
pub struct IntoIter<T, N>
where
  N: ArrayLength,
{
  inner: GenericArrayDeque<T, N>,
}

impl<T, N: ArrayLength> IntoIter<T, N> {
  pub(super) fn new(inner: GenericArrayDeque<T, N>) -> Self {
    IntoIter { inner }
  }
}

impl<T: fmt::Debug, N: ArrayLength> fmt::Debug for IntoIter<T, N> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.debug_tuple("IntoIter").field(&self.inner).finish()
  }
}

impl<T, N: ArrayLength> Iterator for IntoIter<T, N> {
  type Item = T;

  #[inline]
  fn next(&mut self) -> Option<T> {
    self.inner.pop_front()
  }

  #[inline]
  fn size_hint(&self) -> (usize, Option<usize>) {
    let len = self.inner.len();
    (len, Some(len))
  }

  #[inline]
  fn count(self) -> usize {
    self.inner.len
  }

  #[inline]
  fn last(mut self) -> Option<Self::Item> {
    self.inner.pop_back()
  }
}

impl<T, N: ArrayLength> DoubleEndedIterator for IntoIter<T, N> {
  #[inline]
  fn next_back(&mut self) -> Option<T> {
    self.inner.pop_back()
  }
}

impl<T, N: ArrayLength> ExactSizeIterator for IntoIter<T, N> {
  #[inline]
  fn len(&self) -> usize {
    self.inner.len()
  }
}

impl<T, N: ArrayLength> FusedIterator for IntoIter<T, N> {}

#[cfg(test)]
mod tests {
  use super::IntoIter;
  use crate::{
    typenum::{U4, U8},
    GenericArrayDeque,
  };

  #[test]
  fn iterator_behaves_like_queue() {
    let mut deque = GenericArrayDeque::<_, U8>::new();
    for value in 0..5 {
      assert!(deque.push_back(value).is_none());
    }

    let mut iter = IntoIter::new(deque.clone());
    assert_eq!(iter.size_hint(), (5, Some(5)));
    assert_eq!(iter.next(), Some(0));
    assert_eq!(iter.next_back(), Some(4));
    assert_eq!(iter.len(), 3);
    assert_eq!(iter.last(), Some(3));

    let count = deque.into_iter().count();
    assert_eq!(count, 5);
  }

  #[test]
  fn fold_and_last_cover_all_items() {
    let mut deque = GenericArrayDeque::<_, U4>::new();
    for value in 0..4 {
      assert!(deque.push_back(value).is_none());
    }
    let sum = IntoIter::new(deque.clone()).fold(0, |acc, value| acc + value);
    assert_eq!(sum, 6);

    let last = IntoIter::new(deque).last();
    assert_eq!(last, Some(3));
  }

  #[test]
  fn size_hint_shrinks_as_items_consumed() {
    let mut deque = GenericArrayDeque::<_, U4>::new();
    for value in 0..4 {
      assert!(deque.push_back(value).is_none());
    }
    let mut iter = IntoIter::new(deque);
    assert_eq!(iter.size_hint(), (4, Some(4)));
    iter.next();
    assert_eq!(iter.size_hint(), (3, Some(3)));
    iter.next_back();
    assert_eq!(iter.size_hint(), (2, Some(2)));
  }
}
