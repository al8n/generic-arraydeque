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
