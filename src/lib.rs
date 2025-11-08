//! A template for creating Rust open-source repo on GitHub
#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![cfg_attr(docsrs, allow(unused_attributes))]
// #![deny(missing_docs)]

#[cfg(all(not(feature = "std"), feature = "alloc"))]
extern crate alloc as std;

#[cfg(feature = "std")]
extern crate std;

use core::{
  cmp::Ordering,
  fmt,
  hash::{Hash, Hasher},
  iter::{repeat_n, repeat_with},
  mem::{self, ManuallyDrop, MaybeUninit},
  ops::{Index, IndexMut, Range},
  ptr, slice,
};
use generic_array::GenericArray;

pub use generic_array::{ArrayLength, typenum};
pub use into_iter::IntoIter;
pub use iter::Iter;
pub use iter_mut::IterMut;

mod into_iter;
mod iter;
mod iter_mut;

pub struct GenericArrayVecDeque<T, N>
where
  N: ArrayLength,
{
  array: GenericArray<MaybeUninit<T>, N>,
  head: usize,
  len: usize,
}

impl<T, N> Clone for GenericArrayVecDeque<T, N>
where
  T: Clone,
  N: ArrayLength,
{
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn clone(&self) -> Self {
    let mut deq = Self::new();
    if mem::size_of::<T>() != 0 {
      // SAFETY: ensures that there is enough capacity.
      unsafe {
        ptr::copy_nonoverlapping(self.array.as_ptr(), deq.ptr_mut() as _, N::USIZE);
      }
    }
    deq.head = self.head;
    deq.len = self.len;
    deq
  }
}

impl<T, N> Default for GenericArrayVecDeque<T, N>
where
  N: ArrayLength,
{
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn default() -> Self {
    Self::new()
  }
}

impl<T: fmt::Debug, N: ArrayLength> fmt::Debug for GenericArrayVecDeque<T, N> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.debug_list().entries(self.iter()).finish()
  }
}

impl<T: PartialEq, N: ArrayLength> PartialEq for GenericArrayVecDeque<T, N> {
  fn eq(&self, other: &Self) -> bool {
    if self.len != other.len() {
      return false;
    }
    let (sa, sb) = self.as_slices();
    let (oa, ob) = other.as_slices();
    if sa.len() == oa.len() {
      sa == oa && sb == ob
    } else if sa.len() < oa.len() {
      // Always divisible in three sections, for example:
      // self:  [a b c|d e f]
      // other: [0 1 2 3|4 5]
      // front = 3, mid = 1,
      // [a b c] == [0 1 2] && [d] == [3] && [e f] == [4 5]
      let front = sa.len();
      let mid = oa.len() - front;

      let (oa_front, oa_mid) = oa.split_at(front);
      let (sb_mid, sb_back) = sb.split_at(mid);
      debug_assert_eq!(sa.len(), oa_front.len());
      debug_assert_eq!(sb_mid.len(), oa_mid.len());
      debug_assert_eq!(sb_back.len(), ob.len());
      sa == oa_front && sb_mid == oa_mid && sb_back == ob
    } else {
      let front = oa.len();
      let mid = sa.len() - front;

      let (sa_front, sa_mid) = sa.split_at(front);
      let (ob_mid, ob_back) = ob.split_at(mid);
      debug_assert_eq!(sa_front.len(), oa.len());
      debug_assert_eq!(sa_mid.len(), ob_mid.len());
      debug_assert_eq!(sb.len(), ob_back.len());
      sa_front == oa && sa_mid == ob_mid && sb == ob_back
    }
  }
}

impl<T: Eq, N: ArrayLength> Eq for GenericArrayVecDeque<T, N> {}

macro_rules! __impl_slice_eq1 {
    ([$($vars:tt)*] $lhs:ty, $rhs:ty, $($constraints:tt)*) => {
        impl<T, U, L: ArrayLength, $($vars)*> PartialEq<$rhs> for $lhs
        where
            T: PartialEq<U>,
            $($constraints)*
        {
            fn eq(&self, other: &$rhs) -> bool {
                if self.len() != other.len() {
                    return false;
                }
                let (sa, sb) = self.as_slices();
                let (oa, ob) = other[..].split_at(sa.len());
                sa == oa && sb == ob
            }
        }
    }
}
#[cfg(any(feature = "std", feature = "alloc"))]
__impl_slice_eq1! { [] GenericArrayVecDeque<T, L>, std::vec::Vec<U>, }
__impl_slice_eq1! { [] GenericArrayVecDeque<T, L>, &[U], }
__impl_slice_eq1! { [] GenericArrayVecDeque<T, L>, &mut [U], }
__impl_slice_eq1! { [const N: usize] GenericArrayVecDeque<T, L>, [U; N], }
__impl_slice_eq1! { [const N: usize] GenericArrayVecDeque<T, L>, &[U; N], }
__impl_slice_eq1! { [const N: usize] GenericArrayVecDeque<T, L>, &mut [U; N], }

impl<T: PartialOrd, N: ArrayLength> PartialOrd for GenericArrayVecDeque<T, N> {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    self.iter().partial_cmp(other.iter())
  }
}

impl<T: Ord, N: ArrayLength> Ord for GenericArrayVecDeque<T, N> {
  #[inline]
  fn cmp(&self, other: &Self) -> Ordering {
    self.iter().cmp(other.iter())
  }
}

impl<T: Hash, N: ArrayLength> Hash for GenericArrayVecDeque<T, N> {
  fn hash<H: Hasher>(&self, state: &mut H) {
    state.write_usize(self.len);
    // It's not possible to use Hash::hash_slice on slices
    // returned by as_slices method as their length can vary
    // in otherwise identical deques.
    //
    // Hasher only guarantees equivalence for the exact same
    // set of calls to its methods.
    self.iter().for_each(|elem| elem.hash(state));
  }
}

impl<T, N: ArrayLength> Index<usize> for GenericArrayVecDeque<T, N> {
  type Output = T;

  #[inline]
  fn index(&self, index: usize) -> &T {
    self.get(index).expect("Out of bounds access")
  }
}

impl<T, N: ArrayLength> IndexMut<usize> for GenericArrayVecDeque<T, N> {
  #[inline]
  fn index_mut(&mut self, index: usize) -> &mut T {
    self.get_mut(index).expect("Out of bounds access")
  }
}

impl<T, N: ArrayLength> IntoIterator for GenericArrayVecDeque<T, N> {
  type Item = T;
  type IntoIter = IntoIter<T, N>;

  /// Consumes the deque into a front-to-back iterator yielding elements by
  /// value.
  fn into_iter(self) -> IntoIter<T, N> {
    IntoIter::new(self)
  }
}

impl<'a, T, N: ArrayLength> IntoIterator for &'a GenericArrayVecDeque<T, N> {
  type Item = &'a T;
  type IntoIter = Iter<'a, T>;

  fn into_iter(self) -> Iter<'a, T> {
    self.iter()
  }
}

impl<'a, T, N: ArrayLength> IntoIterator for &'a mut GenericArrayVecDeque<T, N> {
  type Item = &'a mut T;
  type IntoIter = IterMut<'a, T>;

  fn into_iter(self) -> IterMut<'a, T> {
    self.iter_mut()
  }
}

impl<T, N: ArrayLength> From<GenericArray<T, N>> for GenericArrayVecDeque<T, N> {
  fn from(arr: GenericArray<T, N>) -> Self {
    let mut deq = Self::new();
    let arr = ManuallyDrop::new(arr);
    if mem::size_of::<T>() != 0 {
      // SAFETY: ensures that there is enough capacity.
      unsafe {
        ptr::copy_nonoverlapping(arr.as_ptr(), deq.ptr_mut() as _, N::USIZE);
      }
    }
    deq.head = 0;
    deq.len = N::USIZE;
    deq
  }
}

macro_rules! insert {
  ($this:ident($index:ident, $value:ident)) => {{
    let k = $this.len - $index;
    if k < $index {
      // `index + 1` can't overflow, because if index was usize::MAX, then either the
      // assert would've failed, or the deque would've tried to grow past usize::MAX
      // and panicked.
      unsafe {
        // see `remove()` for explanation why this wrap_copy() call is safe.
        $this.wrap_copy(
          $this.to_physical_idx($index),
          $this.to_physical_idx($index + 1),
          k,
        );
        $this.len += 1;
        $this.buffer_write($this.to_physical_idx($index), $value)
      }
    } else {
      let old_head = $this.head;
      $this.head = $this.wrap_sub($this.head, 1);
      unsafe {
        $this.wrap_copy(old_head, $this.head, $index);
        $this.len += 1;
        $this.buffer_write($this.to_physical_idx($index), $value)
      }
    }
  }};
}

impl<T, N> GenericArrayVecDeque<T, N>
where
  N: ArrayLength,
{
  /// Creates an empty deque.
  ///
  /// ## Examples
  ///
  /// ```
  /// use generic_arraydeque::{GenericArrayVecDeque, typenum::U8};
  ///
  /// let deque: GenericArrayVecDeque<u32, U8> = GenericArrayVecDeque::new();
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn new() -> Self {
    Self {
      array: GenericArray::uninit(),
      head: 0,
      len: 0,
    }
  }

  /// Tries to create a deque from an iterator.
  ///
  /// If the iterator yields more elements than the capacity of the deque,
  /// the remaining elements will be returned as an `Err` value.
  ///
  /// See also [`try_from_exact_iter`] which requires the iterator to yield exactly
  /// the same number of elements as the capacity of the deque.
  pub fn try_from_iter<I: IntoIterator<Item = T>>(iter: I) -> Result<Self, I::IntoIter> {
    let mut deq = Self::new();
    let mut iterator = iter.into_iter();
    for idx in 0..N::USIZE {
      match iterator.next() {
        Some(value) => {
          deq.array[idx].write(value);
          deq.len += 1;
        }
        None => return Ok(deq),
      }
    }
    Err(iterator)
  }

  /// Tries to create a deque from an iterator.
  ///
  /// If the iterator does not yield exactly the same number of elements
  /// as the capacity of the deque, the iterator will be returned as an `Err` value.
  pub fn try_from_exact_iter<I>(iter: I) -> Result<Self, I::IntoIter>
  where
    I: IntoIterator<Item = T>,
    I::IntoIter: ExactSizeIterator,
  {
    let iter = iter.into_iter();
    if iter.len() > N::USIZE {
      return Err(iter);
    }

    let mut deq = Self::new();
    for (idx, value) in iter.enumerate() {
      deq.array[idx].write(value);
      deq.len += 1;
    }
    Ok(deq)
  }

  /// Creates a deque from an iterator without checking the number of elements and capacity of the deque.
  ///
  /// ## Safety
  /// - The iterator must yield at most `N::USIZE` elements.
  pub unsafe fn from_iter_unchecked<I: IntoIterator<Item = T>>(iter: I) -> Self {
    let mut deq = Self::new();
    let mut iterator = iter.into_iter();
    for idx in 0..N::USIZE {
      match iterator.next() {
        Some(value) => {
          deq.array[idx].write(value);
          deq.len += 1;
        }
        None => break,
      }
    }
    deq
  }

  /// Tries to create a deque from a vector.
  ///
  /// If the vector contains more elements than the capacity of the deque,
  /// the vector will be returned as an `Err` value.
  #[cfg(any(feature = "std", feature = "alloc"))]
  #[cfg_attr(docsrs, doc(cfg(any(feature = "std", feature = "alloc"))))]
  pub fn try_from_vec(vec: Vec<T>) -> Result<Self, std::vec::Vec<T>> {
    if vec.len() > N::USIZE {
      return Err(vec);
    }
    let mut deq = Self::new();
    // SAFETY: We have already checked that the length of the vec is less than or equal to the capacity of the deque.
    unsafe {
      ptr::copy_nonoverlapping(vec.as_ptr(), deq.ptr_mut() as _, vec.len());
    }
    deq.len = vec.len();
    Ok(deq)
  }

  /// Tries to create a deque from an array.
  ///
  /// If the array contains more elements than the capacity of the deque,
  /// the array will be returned as an `Err` value.
  pub fn try_from_array<const SIZE: usize>(arr: [T; SIZE]) -> Result<Self, [T; SIZE]> {
    if SIZE > N::USIZE {
      return Err(arr);
    }
    let mut deq = Self::new();
    // SAFETY: We have already checked that the length of the array is less than or equal to the capacity of the deque.
    unsafe {
      ptr::copy_nonoverlapping(arr.as_ptr(), deq.ptr_mut() as _, SIZE);
    }
    deq.len = SIZE;
    Ok(deq)
  }

  /// Returns the capacity of the deque.
  ///
  /// ## Examples
  ///
  /// ```
  /// use generic_arraydeque::{GenericArrayVecDeque, typenum::U8};
  ///
  /// let deque: GenericArrayVecDeque<u32, U8> = GenericArrayVecDeque::new();
  /// assert_eq!(deque.capacity(), 8);
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn capacity(&self) -> usize {
    N::USIZE
  }

  /// Returns the number of elements in the deque.
  ///
  /// ## Examples
  ///
  /// ```
  /// use generic_arraydeque::{GenericArrayVecDeque, typenum::U8};
  ///
  /// let mut deque = GenericArrayVecDeque::<u32, U8>::new();
  /// assert_eq!(deque.len(), 0);
  /// deque.push_back(1);
  /// assert_eq!(deque.len(), 1);
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn len(&self) -> usize {
    self.len
  }

  /// Returns `true` if the deque is empty.
  ///
  /// ## Examples
  ///
  /// ```
  /// use generic_arraydeque::{GenericArrayVecDeque, typenum::U8};
  ///
  /// let mut deque = GenericArrayVecDeque::<u32, U8>::new();
  /// assert!(deque.is_empty());
  /// deque.push_front(1);
  /// assert!(!deque.is_empty());
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn is_empty(&self) -> bool {
    self.len == 0
  }

  /// Returns `true` if the deque is at full capacity.
  ///
  /// ## Examples
  ///
  /// ```
  /// use generic_arraydeque::{GenericArrayVecDeque, typenum::U2};
  ///
  /// let mut deque: GenericArrayVecDeque<u32, U2> = GenericArrayVecDeque::new();
  /// assert!(!deque.is_full());
  /// deque.push_back(10).unwrap();
  /// assert!(!deque.is_full());
  /// deque.push_back(20).unwrap();
  /// assert!(deque.is_full());
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn is_full(&self) -> bool {
    self.len == self.capacity()
  }

  /// Returns a front-to-back iterator.
  ///
  /// # Examples
  ///
  /// ```
  /// use std::collections::VecDeque;
  ///
  /// let mut buf = VecDeque::new();
  /// buf.push_back(5);
  /// buf.push_back(3);
  /// buf.push_back(4);
  /// let b: &[_] = &[&5, &3, &4];
  /// let c: Vec<&i32> = buf.iter().collect();
  /// assert_eq!(&c[..], b);
  /// ```
  pub fn iter(&self) -> Iter<'_, T> {
    let (a, b) = self.as_slices();
    Iter::new(a.iter(), b.iter())
  }

  /// Returns a front-to-back iterator that returns mutable references.
  ///
  /// # Examples
  ///
  /// ```
  /// use std::collections::VecDeque;
  ///
  /// let mut buf = VecDeque::new();
  /// buf.push_back(5);
  /// buf.push_back(3);
  /// buf.push_back(4);
  /// for num in buf.iter_mut() {
  ///     *num = *num - 2;
  /// }
  /// let b: &[_] = &[&mut 3, &mut 1, &mut 2];
  /// assert_eq!(&buf.iter_mut().collect::<Vec<&mut i32>>()[..], b);
  /// ```
  pub fn iter_mut(&mut self) -> IterMut<'_, T> {
    let (a, b) = self.as_mut_slices();
    IterMut::new(a.iter_mut(), b.iter_mut())
  }

  /// Returns a pair of slices which contain, in order, the contents of the
  /// deque.
  ///
  /// If [`make_contiguous`] was previously called, all elements of the
  /// deque will be in the first slice and the second slice will be empty.
  /// Otherwise, the exact split point depends on implementation details
  /// and is not guaranteed.
  ///
  /// [`make_contiguous`]: VecDeque::make_contiguous
  ///
  /// ## Examples
  ///
  /// ```
  /// use generic_arraydeque::{GenericArrayVecDeque, typenum::U8};
  ///
  /// let mut deque = GenericArrayVecDeque::<u32, U8>::new();
  ///
  /// deque.push_back(0);
  /// deque.push_back(1);
  /// deque.push_back(2);
  ///
  /// let expected = [0, 1, 2];
  /// let (front, back) = deque.as_slices();
  /// assert_eq!(&expected[..front.len()], front);
  /// assert_eq!(&expected[front.len()..], back);
  ///
  /// deque.push_front(10);
  /// deque.push_front(9);
  ///
  /// let expected = [9, 10, 0, 1, 2];
  /// let (front, back) = deque.as_slices();
  /// assert_eq!(&expected[..front.len()], front);
  /// assert_eq!(&expected[front.len()..], back);
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn as_slices(&self) -> (&[T], &[T]) {
    let (a_range, b_range) = self.slice_full_ranges();
    // SAFETY: `slice_full_ranges` always returns valid ranges into
    // the physical buffer.
    unsafe { (&*self.buffer_range(a_range), &*self.buffer_range(b_range)) }
  }

  /// Returns a pair of slices which contain, in order, the contents of the
  /// deque.
  ///
  /// If [`make_contiguous`] was previously called, all elements of the
  /// deque will be in the first slice and the second slice will be empty.
  /// Otherwise, the exact split point depends on implementation details
  /// and is not guaranteed.
  ///
  /// [`make_contiguous`]: VecDeque::make_contiguous
  ///
  /// ## Examples
  ///
  /// ```
  /// use generic_arraydeque::{GenericArrayVecDeque, typenum::U8};
  ///
  /// let mut deque = GenericArrayVecDeque::<u32, U8>::new();
  ///
  /// deque.push_back(0);
  /// deque.push_back(1);
  ///
  /// deque.push_front(10);
  /// deque.push_front(9);
  ///
  /// // Since the split point is not guaranteed, we may need to update
  /// // either slice.
  /// let mut update_nth = |index: usize, val: u32| {
  ///     let (front, back) = deque.as_mut_slices();
  ///     if index > front.len() - 1 {
  ///         back[index - front.len()] = val;
  ///     } else {
  ///         front[index] = val;
  ///     }
  /// };
  ///
  /// update_nth(0, 42);
  /// update_nth(2, 24);
  ///
  /// let v: Vec<_> = deque.into();
  /// assert_eq!(v, [42, 10, 24, 1]);
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn as_mut_slices(&mut self) -> (&mut [T], &mut [T]) {
    let (a_range, b_range) = self.slice_full_ranges();
    // SAFETY: `slice_full_ranges` always returns valid ranges into
    // the physical buffer.
    unsafe {
      (
        &mut *self.buffer_range_mut(a_range),
        &mut *self.buffer_range_mut(b_range),
      )
    }
  }

  /// Provides a reference to the front element, or `None` if the deque is
  /// empty.
  ///
  /// ## Examples
  ///
  /// ```
  /// use generic_arraydeque::{GenericArrayVecDeque, typenum::U8};
  ///
  /// let mut d = GenericArrayVecDeque::<u32, U8>::new();
  /// assert_eq!(d.front(), None);
  ///
  /// d.push_back(1);
  /// d.push_back(2);
  /// assert_eq!(d.front(), Some(&1));
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn front(&self) -> Option<&T> {
    self.get(0)
  }

  /// Provides a mutable reference to the front element, or `None` if the
  /// deque is empty.
  ///
  /// ## Examples
  ///
  /// ```
  /// use generic_arraydeque::{GenericArrayVecDeque, typenum::U8};
  ///
  /// let mut d = GenericArrayVecDeque::<u32, U8>::new();
  /// assert_eq!(d.front_mut(), None);
  ///
  /// d.push_back(1);
  /// d.push_back(2);
  /// match d.front_mut() {
  ///     Some(x) => *x = 9,
  ///     None => (),
  /// }
  /// assert_eq!(d.front(), Some(&9));
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn front_mut(&mut self) -> Option<&mut T> {
    self.get_mut(0)
  }

  /// Provides a reference to the back element, or `None` if the deque is
  /// empty.
  ///
  /// ## Examples
  ///
  /// ```
  /// use generic_arraydeque::{GenericArrayVecDeque, typenum::U8};
  ///
  /// let mut d = GenericArrayVecDeque::<u32, U8>::new();
  /// assert_eq!(d.back(), None);
  ///
  /// d.push_back(1);
  /// d.push_back(2);
  /// assert_eq!(d.back(), Some(&2));
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn back(&self) -> Option<&T> {
    self.get(self.len.wrapping_sub(1))
  }

  /// Provides a mutable reference to the back element, or `None` if the
  /// deque is empty.
  ///
  /// ## Examples
  ///
  /// ```
  /// use generic_arraydeque::{GenericArrayVecDeque, typenum::U8};
  ///
  /// let mut d = GenericArrayVecDeque::<u32, U8>::new();
  /// assert_eq!(d.back(), None);
  ///
  /// d.push_back(1);
  /// d.push_back(2);
  /// match d.back_mut() {
  ///     Some(x) => *x = 9,
  ///     None => (),
  /// }
  /// assert_eq!(d.back(), Some(&9));
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn back_mut(&mut self) -> Option<&mut T> {
    self.get_mut(self.len.wrapping_sub(1))
  }

  /// Provides a reference to the element at the given index.
  ///
  /// Elements at index 0 is the front of the deque.
  ///
  /// ## Examples
  ///
  /// ```
  /// use generic_arraydeque::{GenericArrayVecDeque, typenum::U8};
  ///
  /// let mut deque: GenericArrayVecDeque<u32, U8> = GenericArrayVecDeque::new();
  /// deque.push_back(10).unwrap();
  /// deque.push_back(20).unwrap();
  /// assert_eq!(*deque.get(0).unwrap(), 10);
  /// assert_eq!(*deque.get(1).unwrap(), 20);
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn get(&self, index: usize) -> Option<&T> {
    if index < self.len {
      let idx = self.to_physical_idx(index);
      // SAFETY: index is checked to be in-bounds
      unsafe { Some((&*self.ptr().add(idx)).assume_init_ref()) }
    } else {
      None
    }
  }

  /// Provides a mutable reference to the element at the given index.
  ///
  /// Elements at index 0 is the front of the deque.
  ///
  /// ## Examples
  ///
  /// ```
  /// use generic_arraydeque::{GenericArrayVecDeque, typenum::U8};
  ///
  /// let mut deque: GenericArrayVecDeque<u32, U8> = GenericArrayVecDeque::new();
  /// deque.push_back(10).unwrap();
  /// deque.push_back(20).unwrap();
  /// *deque.get_mut(0).unwrap() += 5;
  /// assert_eq!(*deque.get(0).unwrap(), 15);
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn get_mut(&mut self, index: usize) -> Option<&mut T> {
    if index < self.len {
      let idx = self.to_physical_idx(index);
      // SAFETY: index is checked to be in-bounds
      unsafe { Some((&mut *self.ptr_mut().add(idx)).assume_init_mut()) }
    } else {
      None
    }
  }

  /// Appends an element to the back of the deque, returning `None` if successful.
  ///
  /// If the deque is at full capacity, returns the element back without modifying the deque.
  ///
  /// ## Examples
  ///
  /// ```
  /// use generic_arraydeque::{GenericArrayVecDeque, typenum::U2};
  ///
  /// let mut deque: GenericArrayVecDeque<u32, U2> = GenericArrayVecDeque::new();
  /// assert!(deque.push_back(10).is_none());
  /// assert!(deque.push_back(20).is_none());
  /// assert!(deque.push_back(30).is_some());
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn push_back(&mut self, value: T) -> Option<T> {
    if self.is_full() {
      Some(value)
    } else {
      let len = self.len;
      self.len += 1;
      let idx = self.to_physical_idx(len);

      // SAFETY: idx is guaranteed to be in-bounds and uninitialized
      unsafe {
        let ptr = &mut *self.ptr_mut().add(idx);
        ptr.write(value);
        None
      }
    }
  }

  /// Removes the first element and returns it, or `None` if the deque is
  /// empty.
  ///
  /// ## Examples
  ///
  /// ```
  /// use generic_arraydeque::{GenericArrayVecDeque, typenum::U8};
  ///
  /// let mut d = GenericArrayVecDeque::<u32, U8>::new();
  /// d.push_back(1);
  /// d.push_back(2);
  ///
  /// assert_eq!(d.pop_front(), Some(1));
  /// assert_eq!(d.pop_front(), Some(2));
  /// assert_eq!(d.pop_front(), None);
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn pop_front(&mut self) -> Option<T> {
    if self.is_empty() {
      None
    } else {
      let old_head = self.head;
      self.head = self.to_physical_idx(1);
      self.len -= 1;
      unsafe {
        core::hint::assert_unchecked(self.len < self.capacity());
        Some(self.buffer_read(old_head))
      }
    }
  }

  /// Removes and returns the first element from the deque if the predicate
  /// returns `true`, or [`None`] if the predicate returns false or the deque
  /// is empty (the predicate will not be called in that case).
  ///
  /// # Examples
  ///
  /// ```
  /// #![feature(vec_deque_pop_if)]
  /// use std::collections::VecDeque;
  ///
  /// let mut deque: VecDeque<i32> = vec![0, 1, 2, 3, 4].into();
  /// let pred = |x: &mut i32| *x % 2 == 0;
  ///
  /// assert_eq!(deque.pop_front_if(pred), Some(0));
  /// assert_eq!(deque, [1, 2, 3, 4]);
  /// assert_eq!(deque.pop_front_if(pred), None);
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn pop_front_if(&mut self, predicate: impl FnOnce(&mut T) -> bool) -> Option<T> {
    let first = self.front_mut()?;
    if predicate(first) {
      self.pop_front()
    } else {
      None
    }
  }

  /// Removes the last element from the deque and returns it, or `None` if
  /// it is empty.
  ///
  /// ## Examples
  ///
  /// ```
  /// use generic_arraydeque::{GenericArrayVecDeque, typenum::U8};
  ///
  /// let mut buf = GenericArrayVecDeque::<u32, U8>::new();
  /// assert_eq!(buf.pop_back(), None);
  /// buf.push_back(1);
  /// buf.push_back(3);
  /// assert_eq!(buf.pop_back(), Some(3));
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn pop_back(&mut self) -> Option<T> {
    if self.is_empty() {
      None
    } else {
      self.len -= 1;
      unsafe {
        core::hint::assert_unchecked(self.len < self.capacity());
        Some(self.buffer_read(self.to_physical_idx(self.len)))
      }
    }
  }

  /// Removes and returns the last element from the deque if the predicate
  /// returns `true`, or [`None`] if the predicate returns false or the deque
  /// is empty (the predicate will not be called in that case).
  ///
  /// # Examples
  ///
  /// ```
  /// #![feature(vec_deque_pop_if)]
  /// use std::collections::VecDeque;
  ///
  /// let mut deque: VecDeque<i32> = vec![0, 1, 2, 3, 4].into();
  /// let pred = |x: &mut i32| *x % 2 == 0;
  ///
  /// assert_eq!(deque.pop_back_if(pred), Some(4));
  /// assert_eq!(deque, [0, 1, 2, 3]);
  /// assert_eq!(deque.pop_back_if(pred), None);
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn pop_back_if(&mut self, predicate: impl FnOnce(&mut T) -> bool) -> Option<T> {
    let first = self.back_mut()?;
    if predicate(first) {
      self.pop_back()
    } else {
      None
    }
  }

  /// Appends an element to the back of the deque, returning a mutable reference to it if successful.
  ///
  /// If the deque is at full capacity, returns the element back without modifying the deque.
  ///
  /// ## Examples
  ///
  /// ```
  /// use generic_arraydeque::{GenericArrayVecDeque, typenum::U2};
  ///
  /// let mut deque: GenericArrayVecDeque<u32, U2> = GenericArrayVecDeque::new();
  /// let elem_ref = deque.push_back_mut(10).unwrap();
  /// *elem_ref += 5;
  /// assert_eq!(*deque.get(0).unwrap(), 15);
  /// let _ = deque.push_back_mut(20).unwrap();
  /// assert!(deque.push_back_mut(30).is_err());
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn push_back_mut(&mut self, value: T) -> Result<&mut T, T> {
    if self.is_full() {
      Err(value)
    } else {
      let len = self.len;
      self.len += 1;
      let idx = self.to_physical_idx(len);

      // SAFETY: idx is guaranteed to be in-bounds and uninitialized
      unsafe {
        let ptr = &mut *self.ptr_mut().add(idx);
        ptr.write(value);
        Ok(ptr.assume_init_mut())
      }
    }
  }

  /// Prepends an element to the front of the deque, returning `None` if successful.
  ///
  /// If the deque is at full capacity, returns the element back without modifying the deque.
  ///
  /// ## Examples
  ///
  /// ```
  /// use generic_arraydeque::{GenericArrayVecDeque, typenum::U2};
  ///
  /// let mut deque: GenericArrayVecDeque<u32, U2> = GenericArrayVecDeque::new();
  ///
  /// assert!(deque.push_front(10).is_none());
  /// assert!(deque.push_front(20).is_none());
  /// assert!(deque.push_front(30).is_some());
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn push_front(&mut self, value: T) -> Option<T> {
    if self.is_full() {
      Some(value)
    } else {
      self.head = self.wrap_sub(self.head, 1);
      self.len += 1;
      // SAFETY: head is guaranteed to be in-bounds and uninitialized
      unsafe {
        let ptr = &mut *self.ptr_mut().add(self.head);
        ptr.write(value);
        None
      }
    }
  }

  /// Prepends an element to the front of the deque, returning a mutable reference to it if successful.
  ///
  /// If the deque is at full capacity, returns the element back without modifying the deque.
  ///
  /// ## Examples
  ///
  /// ```
  /// use generic_arraydeque::{GenericArrayVecDeque, typenum::U2};
  ///
  /// let mut deque: GenericArrayVecDeque<u32, U2> = GenericArrayVecDeque::new();
  /// let elem_ref = deque.push_front_mut(10).unwrap();
  /// *elem_ref += 5;
  /// assert_eq!(*deque.get(0).unwrap(), 15);
  /// let _ = deque.push_front_mut(20).unwrap();
  /// assert!(deque.push_front_mut(30).is_err());
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn push_front_mut(&mut self, value: T) -> Result<&mut T, T> {
    if self.is_full() {
      Err(value)
    } else {
      self.head = self.wrap_sub(self.head, 1);
      self.len += 1;
      // SAFETY: head is guaranteed to be in-bounds and uninitialized
      unsafe {
        let ptr = &mut *self.ptr_mut().add(self.head);
        ptr.write(value);
        Ok(ptr.assume_init_mut())
      }
    }
  }

  /// Rotates the double-ended queue `n` places to the left.
  ///
  /// Equivalently,
  /// - Rotates item `n` into the first position.
  /// - Pops the first `n` items and pushes them to the end.
  /// - Rotates `len() - n` places to the right.
  ///
  /// ## Panics
  ///
  /// If `n` is greater than `len()`. Note that `n == len()`
  /// does _not_ panic and is a no-op rotation.
  ///
  /// # Complexity
  ///
  /// Takes `*O*(min(n, len() - n))` time and no extra space.
  ///
  /// ## Examples
  ///
  /// ```
  /// use generic_arraydeque::{GenericArrayVecDeque, typenum::U10};
  ///
  /// let mut buf: GenericArrayVecDeque<u32, U10> = (0..10).collect();
  ///
  /// buf.rotate_left(3);
  /// assert_eq!(buf, [3, 4, 5, 6, 7, 8, 9, 0, 1, 2]);
  ///
  /// for i in 1..10 {
  ///     assert_eq!(i * 3 % 10, buf[0]);
  ///     buf.rotate_left(3);
  /// }
  /// assert_eq!(buf, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]);
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn rotate_left(&mut self, n: usize) {
    assert!(n <= self.len());
    let k = self.len - n;
    if n <= k {
      unsafe { self.rotate_left_inner(n) }
    } else {
      unsafe { self.rotate_right_inner(k) }
    }
  }

  /// Rotates the double-ended queue `n` places to the right.
  ///
  /// Equivalently,
  /// - Rotates the first item into position `n`.
  /// - Pops the last `n` items and pushes them to the front.
  /// - Rotates `len() - n` places to the left.
  ///
  /// ## Panics
  ///
  /// If `n` is greater than `len()`. Note that `n == len()`
  /// does _not_ panic and is a no-op rotation.
  ///
  /// # Complexity
  ///
  /// Takes `*O*(min(n, len() - n))` time and no extra space.
  ///
  /// ## Examples
  ///
  /// ```
  /// use generic_arraydeque::{GenericArrayVecDeque, typenum::U10};
  ///
  /// let mut buf: GenericArrayVecDeque<u32, U10> = (0..10).collect();
  ///
  /// buf.rotate_right(3);
  /// assert_eq!(buf, [7, 8, 9, 0, 1, 2, 3, 4, 5, 6]);
  ///
  /// for i in 1..10 {
  ///     assert_eq!(0, buf[i * 3 % 10]);
  ///     buf.rotate_right(3);
  /// }
  /// assert_eq!(buf, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]);
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn rotate_right(&mut self, n: usize) {
    assert!(n <= self.len());
    let k = self.len - n;
    if n <= k {
      unsafe { self.rotate_right_inner(n) }
    } else {
      unsafe { self.rotate_left_inner(k) }
    }
  }

  /// Rearranges the internal storage of this deque so it is one contiguous
  /// slice, which is then returned.
  ///
  /// This method does not allocate and does not change the order of the
  /// inserted elements. As it returns a mutable slice, this can be used to
  /// sort a deque.
  ///
  /// Once the internal storage is contiguous, the [`as_slices`] and
  /// [`as_mut_slices`] methods will return the entire contents of the
  /// deque in a single slice.
  ///
  /// [`as_slices`]: VecDeque::as_slices
  /// [`as_mut_slices`]: VecDeque::as_mut_slices
  ///
  /// ## Examples
  ///
  /// Sorting the content of a deque.
  ///
  /// ```
  /// use std::collections::VecDeque;
  ///
  /// let mut buf = VecDeque::with_capacity(15);
  ///
  /// buf.push_back(2);
  /// buf.push_back(1);
  /// buf.push_front(3);
  ///
  /// // sorting the deque
  /// buf.make_contiguous().sort();
  /// assert_eq!(buf.as_slices(), (&[1, 2, 3] as &[_], &[] as &[_]));
  ///
  /// // sorting it in reverse order
  /// buf.make_contiguous().sort_by(|a, b| b.cmp(a));
  /// assert_eq!(buf.as_slices(), (&[3, 2, 1] as &[_], &[] as &[_]));
  /// ```
  ///
  /// Getting immutable access to the contiguous slice.
  ///
  /// ```rust
  /// use std::collections::VecDeque;
  ///
  /// let mut buf = VecDeque::new();
  ///
  /// buf.push_back(2);
  /// buf.push_back(1);
  /// buf.push_front(3);
  ///
  /// buf.make_contiguous();
  /// if let (slice, &[]) = buf.as_slices() {
  ///     // we can now be sure that `slice` contains all elements of the deque,
  ///     // while still having immutable access to `buf`.
  ///     assert_eq!(buf.len(), slice.len());
  ///     assert_eq!(slice, &[3, 2, 1] as &[_]);
  /// }
  /// ```
  pub const fn make_contiguous(&mut self) -> &mut [T] {
    if mem::size_of::<T>() == 0 {
      self.head = 0;
    }

    if self.is_contiguous() {
      unsafe { return slice::from_raw_parts_mut(self.ptr().add(self.head) as _, self.len) }
    }

    let &mut Self { head, len, .. } = self;
    let ptr = self.ptr();
    let cap = self.capacity();

    let free = cap - len;
    let head_len = cap - head;
    let tail = len - head_len;
    let tail_len = tail;

    if free >= head_len {
      // there is enough free space to copy the head in one go,
      // this means that we first shift the tail backwards, and then
      // copy the head to the correct position.
      //
      // from: DEFGH....ABC
      // to:   ABCDEFGH....
      unsafe {
        self.copy(0, head_len, tail_len);
        // ...DEFGH.ABC
        self.copy_nonoverlapping(head, 0, head_len);
        // ABCDEFGH....
      }

      self.head = 0;
    } else if free >= tail_len {
      // there is enough free space to copy the tail in one go,
      // this means that we first shift the head forwards, and then
      // copy the tail to the correct position.
      //
      // from: FGH....ABCDE
      // to:   ...ABCDEFGH.
      unsafe {
        self.copy(head, tail, head_len);
        // FGHABCDE....
        self.copy_nonoverlapping(0, tail + head_len, tail_len);
        // ...ABCDEFGH.
      }

      self.head = tail;
    } else {
      // `free` is smaller than both `head_len` and `tail_len`.
      // the general algorithm for this first moves the slices
      // right next to each other and then uses `slice::rotate`
      // to rotate them into place:
      //
      // initially:   HIJK..ABCDEFG
      // step 1:      ..HIJKABCDEFG
      // step 2:      ..ABCDEFGHIJK
      //
      // or:
      //
      // initially:   FGHIJK..ABCDE
      // step 1:      FGHIJKABCDE..
      // step 2:      ABCDEFGHIJK..

      // pick the shorter of the 2 slices to reduce the amount
      // of memory that needs to be moved around.
      if head_len > tail_len {
        // tail is shorter, so:
        //  1. copy tail forwards
        //  2. rotate used part of the buffer
        //  3. update head to point to the new beginning (which is just `free`)

        unsafe {
          // if there is no free space in the buffer, then the slices are already
          // right next to each other and we don't need to move any memory.
          if free != 0 {
            // because we only move the tail forward as much as there's free space
            // behind it, we don't overwrite any elements of the head slice, and
            // the slices end up right next to each other.
            self.copy(0, free, tail_len);
          }

          // We just copied the tail right next to the head slice,
          // so all of the elements in the range are initialized
          let slice = &mut *self.buffer_range_mut(free..self.capacity());

          // because the deque wasn't contiguous, we know that `tail_len < self.len == slice.len()`,
          // so this will never panic.
          slice.rotate_left(tail_len);

          // the used part of the buffer now is `free..self.capacity()`, so set
          // `head` to the beginning of that range.
          self.head = free;
        }
      } else {
        // head is shorter so:
        //  1. copy head backwards
        //  2. rotate used part of the buffer
        //  3. update head to point to the new beginning (which is the beginning of the buffer)

        unsafe {
          // if there is no free space in the buffer, then the slices are already
          // right next to each other and we don't need to move any memory.
          if free != 0 {
            // copy the head slice to lie right behind the tail slice.
            self.copy(self.head, tail_len, head_len);
          }

          // because we copied the head slice so that both slices lie right
          // next to each other, all the elements in the range are initialized.
          let slice = &mut *self.buffer_range_mut(0..self.len);

          // because the deque wasn't contiguous, we know that `head_len < self.len == slice.len()`
          // so this will never panic.
          slice.rotate_right(head_len);

          // the used part of the buffer now is `0..self.len`, so set
          // `head` to the beginning of that range.
          self.head = 0;
        }
      }
    }

    unsafe { slice::from_raw_parts_mut(ptr.add(self.head) as _, self.len) }
  }

  /// Shortens the deque, keeping the first `len` elements and dropping
  /// the rest.
  ///
  /// If `len` is greater or equal to the deque's current length, this has
  /// no effect.
  ///
  /// ## Examples
  ///
  /// ```
  /// use generic_arraydeque::{GenericArrayVecDeque, typenum::U8};
  ///
  /// let mut buf = GenericArrayVecDeque::<u32, U8>::new();
  /// buf.push_back(5);
  /// buf.push_back(10);
  /// buf.push_back(15);
  /// assert_eq!(buf, [5, 10, 15]);
  /// buf.truncate(1);
  /// assert_eq!(buf, [5]);
  /// ```
  pub fn truncate(&mut self, len: usize) {
    /// Runs the destructor for all items in the slice when it gets dropped (normally or
    /// during unwinding).
    struct Dropper<'a, T>(&'a mut [T]);

    impl<T> Drop for Dropper<'_, T> {
      fn drop(&mut self) {
        unsafe {
          ptr::drop_in_place(self.0);
        }
      }
    }

    // Safe because:
    //
    // * Any slice passed to `drop_in_place` is valid; the second case has
    //   `len <= front.len()` and returning on `len > self.len()` ensures
    //   `begin <= back.len()` in the first case
    // * The head of the VecDeque is moved before calling `drop_in_place`,
    //   so no value is dropped twice if `drop_in_place` panics
    unsafe {
      if len >= self.len {
        return;
      }

      let (front, back) = self.as_mut_slices();
      if len > front.len() {
        let begin = len - front.len();
        let drop_back = back.get_unchecked_mut(begin..) as *mut _;
        self.len = len;
        ptr::drop_in_place(drop_back);
      } else {
        let drop_back = back as *mut _;
        let drop_front = front.get_unchecked_mut(len..) as *mut _;
        self.len = len;

        // Make sure the second half is dropped even when a destructor
        // in the first one panics.
        let _back_dropper = Dropper(&mut *drop_back);
        ptr::drop_in_place(drop_front);
      }
    }
  }

  /// Shortens the deque, keeping the last `len` elements and dropping
  /// the rest.
  ///
  /// If `len` is greater or equal to the deque's current length, this has
  /// no effect.
  ///
  /// # Examples
  ///
  /// ```
  /// # #![feature(vec_deque_truncate_front)]
  /// use std::collections::VecDeque;
  ///
  /// let mut buf = VecDeque::new();
  /// buf.push_front(5);
  /// buf.push_front(10);
  /// buf.push_front(15);
  /// assert_eq!(buf, [15, 10, 5]);
  /// assert_eq!(buf.as_slices(), (&[15, 10, 5][..], &[][..]));
  /// buf.truncate_front(1);
  /// assert_eq!(buf.as_slices(), (&[5][..], &[][..]));
  /// ```
  pub fn truncate_front(&mut self, len: usize) {
    /// Runs the destructor for all items in the slice when it gets dropped (normally or
    /// during unwinding).
    struct Dropper<'a, T>(&'a mut [T]);

    impl<T> Drop for Dropper<'_, T> {
      fn drop(&mut self) {
        unsafe {
          ptr::drop_in_place(self.0);
        }
      }
    }

    unsafe {
      if len >= self.len {
        // No action is taken
        return;
      }

      let (front, back) = self.as_mut_slices();
      if len > back.len() {
        // The 'back' slice remains unchanged.
        // front.len() + back.len() == self.len, so 'end' is non-negative
        // and end < front.len()
        let end = front.len() - (len - back.len());
        let drop_front = front.get_unchecked_mut(..end) as *mut _;
        self.head += end;
        self.len = len;
        ptr::drop_in_place(drop_front);
      } else {
        let drop_front = front as *mut _;
        // 'end' is non-negative by the condition above
        let end = back.len() - len;
        let drop_back = back.get_unchecked_mut(..end) as *mut _;
        self.head = self.to_physical_idx(self.len - len);
        self.len = len;

        // Make sure the second half is dropped even when a destructor
        // in the first one panics.
        let _back_dropper = Dropper(&mut *drop_back);
        ptr::drop_in_place(drop_front);
      }
    }
  }

  /// Clears the deque, removing all values.
  ///
  /// ## Examples
  ///
  /// ```
  /// use generic_arraydeque::{GenericArrayVecDeque, typenum::U8};
  ///
  /// let mut deque = GenericArrayVecDeque::<u32, U8>::new();
  /// deque.push_back(1);
  /// deque.clear();
  /// assert!(deque.is_empty());
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn clear(&mut self) {
    self.truncate(0);
    // Not strictly necessary, but leaves things in a more consistent/predictable state.
    self.head = 0;
  }

  /// Returns `true` if the deque contains an element equal to the
  /// given value.
  ///
  /// This operation is *O*(*n*).
  ///
  /// Note that if you have a sorted `VecDeque`, [`binary_search`] may be faster.
  ///
  /// [`binary_search`]: VecDeque::binary_search
  ///
  /// # Examples
  ///
  /// ```
  /// use std::collections::VecDeque;
  ///
  /// let mut deque: VecDeque<u32> = VecDeque::new();
  ///
  /// deque.push_back(0);
  /// deque.push_back(1);
  ///
  /// assert_eq!(deque.contains(&1), true);
  /// assert_eq!(deque.contains(&10), false);
  /// ```
  #[inline]
  pub fn contains(&self, x: &T) -> bool
  where
    T: PartialEq<T>,
  {
    let (a, b) = self.as_slices();
    a.contains(x) || b.contains(x)
  }

  /// Binary searches this `VecDeque` for a given element.
  /// If the `VecDeque` is not sorted, the returned result is unspecified and
  /// meaningless.
  ///
  /// If the value is found then [`Result::Ok`] is returned, containing the
  /// index of the matching element. If there are multiple matches, then any
  /// one of the matches could be returned. If the value is not found then
  /// [`Result::Err`] is returned, containing the index where a matching
  /// element could be inserted while maintaining sorted order.
  ///
  /// See also [`binary_search_by`], [`binary_search_by_key`], and [`partition_point`].
  ///
  /// [`binary_search_by`]: VecDeque::binary_search_by
  /// [`binary_search_by_key`]: VecDeque::binary_search_by_key
  /// [`partition_point`]: VecDeque::partition_point
  ///
  /// ## Examples
  ///
  /// Looks up a series of four elements. The first is found, with a
  /// uniquely determined position; the second and third are not
  /// found; the fourth could match any position in `[1, 4]`.
  ///
  /// ```
  /// use std::collections::VecDeque;
  ///
  /// let deque: VecDeque<_> = [0, 1, 1, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55].into();
  ///
  /// assert_eq!(deque.binary_search(&13),  Ok(9));
  /// assert_eq!(deque.binary_search(&4),   Err(7));
  /// assert_eq!(deque.binary_search(&100), Err(13));
  /// let r = deque.binary_search(&1);
  /// assert!(matches!(r, Ok(1..=4)));
  /// ```
  ///
  /// If you want to insert an item to a sorted deque, while maintaining
  /// sort order, consider using [`partition_point`]:
  ///
  /// ```
  /// use std::collections::VecDeque;
  ///
  /// let mut deque: VecDeque<_> = [0, 1, 1, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55].into();
  /// let num = 42;
  /// let idx = deque.partition_point(|&x| x <= num);
  /// // If `num` is unique, `s.partition_point(|&x| x < num)` (with `<`) is equivalent to
  /// // `s.binary_search(&num).unwrap_or_else(|x| x)`, but using `<=` may allow `insert`
  /// // to shift less elements.
  /// deque.insert(idx, num);
  /// assert_eq!(deque, &[0, 1, 1, 1, 1, 2, 3, 5, 8, 13, 21, 34, 42, 55]);
  /// ```
  #[inline]
  pub fn binary_search(&self, x: &T) -> Result<usize, usize>
  where
    T: Ord,
  {
    self.binary_search_by(|e| e.cmp(x))
  }

  /// Binary searches this `VecDeque` with a comparator function.
  ///
  /// The comparator function should return an order code that indicates
  /// whether its argument is `Less`, `Equal` or `Greater` the desired
  /// target.
  /// If the `VecDeque` is not sorted or if the comparator function does not
  /// implement an order consistent with the sort order of the underlying
  /// `VecDeque`, the returned result is unspecified and meaningless.
  ///
  /// If the value is found then [`Result::Ok`] is returned, containing the
  /// index of the matching element. If there are multiple matches, then any
  /// one of the matches could be returned. If the value is not found then
  /// [`Result::Err`] is returned, containing the index where a matching
  /// element could be inserted while maintaining sorted order.
  ///
  /// See also [`binary_search`], [`binary_search_by_key`], and [`partition_point`].
  ///
  /// [`binary_search`]: VecDeque::binary_search
  /// [`binary_search_by_key`]: VecDeque::binary_search_by_key
  /// [`partition_point`]: VecDeque::partition_point
  ///
  /// ## Examples
  ///
  /// Looks up a series of four elements. The first is found, with a
  /// uniquely determined position; the second and third are not
  /// found; the fourth could match any position in `[1, 4]`.
  ///
  /// ```
  /// use std::collections::VecDeque;
  ///
  /// let deque: VecDeque<_> = [0, 1, 1, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55].into();
  ///
  /// assert_eq!(deque.binary_search_by(|x| x.cmp(&13)),  Ok(9));
  /// assert_eq!(deque.binary_search_by(|x| x.cmp(&4)),   Err(7));
  /// assert_eq!(deque.binary_search_by(|x| x.cmp(&100)), Err(13));
  /// let r = deque.binary_search_by(|x| x.cmp(&1));
  /// assert!(matches!(r, Ok(1..=4)));
  /// ```
  pub fn binary_search_by<'a, F>(&'a self, mut f: F) -> Result<usize, usize>
  where
    F: FnMut(&'a T) -> Ordering,
  {
    let (front, back) = self.as_slices();
    let cmp_back = back.first().map(&mut f);

    if let Some(Ordering::Equal) = cmp_back {
      Ok(front.len())
    } else if let Some(Ordering::Less) = cmp_back {
      back
        .binary_search_by(f)
        .map(|idx| idx + front.len())
        .map_err(|idx| idx + front.len())
    } else {
      front.binary_search_by(f)
    }
  }

  /// Binary searches this `VecDeque` with a key extraction function.
  ///
  /// Assumes that the deque is sorted by the key, for instance with
  /// [`make_contiguous().sort_by_key()`] using the same key extraction function.
  /// If the deque is not sorted by the key, the returned result is
  /// unspecified and meaningless.
  ///
  /// If the value is found then [`Result::Ok`] is returned, containing the
  /// index of the matching element. If there are multiple matches, then any
  /// one of the matches could be returned. If the value is not found then
  /// [`Result::Err`] is returned, containing the index where a matching
  /// element could be inserted while maintaining sorted order.
  ///
  /// See also [`binary_search`], [`binary_search_by`], and [`partition_point`].
  ///
  /// [`make_contiguous().sort_by_key()`]: VecDeque::make_contiguous
  /// [`binary_search`]: VecDeque::binary_search
  /// [`binary_search_by`]: VecDeque::binary_search_by
  /// [`partition_point`]: VecDeque::partition_point
  ///
  /// ## Examples
  ///
  /// Looks up a series of four elements in a slice of pairs sorted by
  /// their second elements. The first is found, with a uniquely
  /// determined position; the second and third are not found; the
  /// fourth could match any position in `[1, 4]`.
  ///
  /// ```
  /// use std::collections::VecDeque;
  ///
  /// let deque: VecDeque<_> = [(0, 0), (2, 1), (4, 1), (5, 1),
  ///          (3, 1), (1, 2), (2, 3), (4, 5), (5, 8), (3, 13),
  ///          (1, 21), (2, 34), (4, 55)].into();
  ///
  /// assert_eq!(deque.binary_search_by_key(&13, |&(a, b)| b),  Ok(9));
  /// assert_eq!(deque.binary_search_by_key(&4, |&(a, b)| b),   Err(7));
  /// assert_eq!(deque.binary_search_by_key(&100, |&(a, b)| b), Err(13));
  /// let r = deque.binary_search_by_key(&1, |&(a, b)| b);
  /// assert!(matches!(r, Ok(1..=4)));
  /// ```
  #[inline]
  pub fn binary_search_by_key<'a, B, F>(&'a self, b: &B, mut f: F) -> Result<usize, usize>
  where
    F: FnMut(&'a T) -> B,
    B: Ord,
  {
    self.binary_search_by(|k| f(k).cmp(b))
  }

  /// Returns the index of the partition point according to the given predicate
  /// (the index of the first element of the second partition).
  ///
  /// The deque is assumed to be partitioned according to the given predicate.
  /// This means that all elements for which the predicate returns true are at the start of the deque
  /// and all elements for which the predicate returns false are at the end.
  /// For example, `[7, 15, 3, 5, 4, 12, 6]` is partitioned under the predicate `x % 2 != 0`
  /// (all odd numbers are at the start, all even at the end).
  ///
  /// If the deque is not partitioned, the returned result is unspecified and meaningless,
  /// as this method performs a kind of binary search.
  ///
  /// See also [`binary_search`], [`binary_search_by`], and [`binary_search_by_key`].
  ///
  /// [`binary_search`]: VecDeque::binary_search
  /// [`binary_search_by`]: VecDeque::binary_search_by
  /// [`binary_search_by_key`]: VecDeque::binary_search_by_key
  ///
  /// ## Examples
  ///
  /// ```
  /// use std::collections::VecDeque;
  ///
  /// let deque: VecDeque<_> = [1, 2, 3, 3, 5, 6, 7].into();
  /// let i = deque.partition_point(|&x| x < 5);
  ///
  /// assert_eq!(i, 4);
  /// assert!(deque.iter().take(i).all(|&x| x < 5));
  /// assert!(deque.iter().skip(i).all(|&x| !(x < 5)));
  /// ```
  ///
  /// If you want to insert an item to a sorted deque, while maintaining
  /// sort order:
  ///
  /// ```
  /// use std::collections::VecDeque;
  ///
  /// let mut deque: VecDeque<_> = [0, 1, 1, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55].into();
  /// let num = 42;
  /// let idx = deque.partition_point(|&x| x < num);
  /// deque.insert(idx, num);
  /// assert_eq!(deque, &[0, 1, 1, 1, 1, 2, 3, 5, 8, 13, 21, 34, 42, 55]);
  /// ```
  pub fn partition_point<P>(&self, mut pred: P) -> usize
  where
    P: FnMut(&T) -> bool,
  {
    let (front, back) = self.as_slices();

    if let Some(true) = back.first().map(&mut pred) {
      back.partition_point(pred) + front.len()
    } else {
      front.partition_point(pred)
    }
  }

  /// Swaps elements at indices `i` and `j`.
  ///
  /// `i` and `j` may be equal.
  ///
  /// Element at index 0 is the front of the queue.
  ///
  /// ## Panics
  ///
  /// Panics if either index is out of bounds.
  ///
  /// ## Examples
  ///
  /// ```
  /// use std::collections::VecDeque;
  ///
  /// let mut buf = VecDeque::new();
  /// buf.push_back(3);
  /// buf.push_back(4);
  /// buf.push_back(5);
  /// assert_eq!(buf, [3, 4, 5]);
  /// buf.swap(0, 2);
  /// assert_eq!(buf, [5, 4, 3]);
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn swap(&mut self, i: usize, j: usize) {
    assert!(i < self.len());
    assert!(j < self.len());
    let ri = self.to_physical_idx(i);
    let rj = self.to_physical_idx(j);
    unsafe { ptr::swap(self.ptr_mut().add(ri), self.ptr_mut().add(rj)) }
  }

  /// Removes an element from anywhere in the deque and returns it,
  /// replacing it with the first element.
  ///
  /// This does not preserve ordering, but is *O*(1).
  ///
  /// Returns `None` if `index` is out of bounds.
  ///
  /// Element at index 0 is the front of the queue.
  ///
  /// ## Examples
  ///
  /// ```
  /// use std::collections::VecDeque;
  ///
  /// let mut buf = VecDeque::new();
  /// assert_eq!(buf.swap_remove_front(0), None);
  /// buf.push_back(1);
  /// buf.push_back(2);
  /// buf.push_back(3);
  /// assert_eq!(buf, [1, 2, 3]);
  ///
  /// assert_eq!(buf.swap_remove_front(2), Some(3));
  /// assert_eq!(buf, [2, 1]);
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn swap_remove_front(&mut self, index: usize) -> Option<T> {
    let length = self.len;
    if index < length && index != 0 {
      self.swap(index, 0);
    } else if index >= length {
      return None;
    }
    self.pop_front()
  }

  /// Removes an element from anywhere in the deque and returns it,
  /// replacing it with the last element.
  ///
  /// This does not preserve ordering, but is *O*(1).
  ///
  /// Returns `None` if `index` is out of bounds.
  ///
  /// Element at index 0 is the front of the queue.
  ///
  /// ## Examples
  ///
  /// ```
  /// use std::collections::VecDeque;
  ///
  /// let mut buf = VecDeque::new();
  /// assert_eq!(buf.swap_remove_back(0), None);
  /// buf.push_back(1);
  /// buf.push_back(2);
  /// buf.push_back(3);
  /// assert_eq!(buf, [1, 2, 3]);
  ///
  /// assert_eq!(buf.swap_remove_back(0), Some(1));
  /// assert_eq!(buf, [3, 2]);
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn swap_remove_back(&mut self, index: usize) -> Option<T> {
    let length = self.len;
    if length > 0 && index < length - 1 {
      self.swap(index, length - 1);
    } else if index >= length {
      return None;
    }
    self.pop_back()
  }

  /// Inserts an element at `index` within the deque, shifting all elements
  /// with indices greater than or equal to `index` towards the back.
  ///
  /// Returns `Some(value)` if `index` is strictly greater than the deque's length or if
  /// the deque is full.
  ///
  /// Element at index 0 is the front of the queue.
  ///
  /// ## Examples
  ///
  /// ```
  /// use std::collections::VecDeque;
  ///
  /// let mut vec_deque = VecDeque::new();
  /// vec_deque.push_back('a');
  /// vec_deque.push_back('b');
  /// vec_deque.push_back('c');
  /// assert_eq!(vec_deque, &['a', 'b', 'c']);
  ///
  /// vec_deque.insert(1, 'd');
  /// assert_eq!(vec_deque, &['a', 'd', 'b', 'c']);
  ///
  /// vec_deque.insert(4, 'e');
  /// assert_eq!(vec_deque, &['a', 'd', 'b', 'c', 'e']);
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn insert(&mut self, index: usize, value: T) -> Option<T> {
    if index <= self.len() || self.is_full() {
      return Some(value);
    }

    let _ = insert!(self(index, value));
    None
  }

  /// Inserts an element at `index` within the deque, shifting all elements
  /// with indices greater than or equal to `index` towards the back, and
  /// returning a reference to it.
  ///
  /// Returns `Err(value)` if `index` is strictly greater than the deque's length or if
  /// the deque is full.
  ///
  /// Element at index 0 is the front of the queue.
  ///
  /// ## Examples
  ///
  /// ```
  /// #![feature(push_mut)]
  /// use std::collections::VecDeque;
  ///
  /// let mut vec_deque = VecDeque::from([1, 2, 3]);
  ///
  /// let x = vec_deque.insert_mut(1, 5);
  /// *x += 7;
  /// assert_eq!(vec_deque, &[1, 12, 2, 3]);
  /// ```
  #[must_use = "if you don't need a reference to the value, use `VecDeque::insert` instead"]
  pub const fn insert_mut(&mut self, index: usize, value: T) -> Result<&mut T, T> {
    if index <= self.len() || self.is_full() {
      return Err(value);
    }

    Ok(insert!(self(index, value)))
  }

  /// Removes and returns the element at `index` from the deque.
  /// Whichever end is closer to the removal point will be moved to make
  /// room, and all the affected elements will be moved to new positions.
  /// Returns `None` if `index` is out of bounds.
  ///
  /// Element at index 0 is the front of the queue.
  ///
  /// ## Examples
  ///
  /// ```
  /// use std::collections::VecDeque;
  ///
  /// let mut buf = VecDeque::new();
  /// buf.push_back('a');
  /// buf.push_back('b');
  /// buf.push_back('c');
  /// assert_eq!(buf, ['a', 'b', 'c']);
  ///
  /// assert_eq!(buf.remove(1), Some('b'));
  /// assert_eq!(buf, ['a', 'c']);
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn remove(&mut self, index: usize) -> Option<T> {
    if self.len <= index {
      return None;
    }

    let wrapped_idx = self.to_physical_idx(index);

    let elem = unsafe { Some(self.buffer_read(wrapped_idx)) };

    let k = self.len - index - 1;
    // safety: due to the nature of the if-condition, whichever wrap_copy gets called,
    // its length argument will be at most `self.len / 2`, so there can't be more than
    // one overlapping area.
    if k < index {
      unsafe { self.wrap_copy(self.wrap_add(wrapped_idx, 1), wrapped_idx, k) };
      self.len -= 1;
    } else {
      let old_head = self.head;
      self.head = self.to_physical_idx(1);
      unsafe { self.wrap_copy(old_head, self.head, index) };
      self.len -= 1;
    }

    elem
  }
}

impl<T, N> GenericArrayVecDeque<T, N>
where
  N: ArrayLength,
  T: Clone,
{
  /// Modifies the deque in-place so that `len()` is equal to new_len,
  /// either by removing excess elements from the back or by appending clones of `value`
  /// to the back.
  ///
  /// If the deque is full and needs to be extended, returns `Some(value)` back, the
  /// deque is not modified in that case.
  ///
  /// # Examples
  ///
  /// ```
  /// use std::collections::VecDeque;
  ///
  /// let mut buf = VecDeque::new();
  /// buf.push_back(5);
  /// buf.push_back(10);
  /// buf.push_back(15);
  /// assert_eq!(buf, [5, 10, 15]);
  ///
  /// buf.resize(2, 0);
  /// assert_eq!(buf, [5, 10]);
  ///
  /// buf.resize(5, 20);
  /// assert_eq!(buf, [5, 10, 20, 20, 20]);
  /// ```
  pub fn resize(&mut self, new_len: usize, value: T) -> Option<T> {
    if new_len > self.capacity() {
      return Some(value);
    }

    if new_len > self.len() {
      let extra = new_len - self.len();
      for v in repeat_n(value, extra) {
        self.push_back(v);
      }
    } else {
      self.truncate(new_len);
    }

    None
  }

  /// Modifies the deque in-place so that `len()` is equal to `new_len`,
  /// either by removing excess elements from the back or by appending
  /// elements generated by calling `generator` to the back.
  ///
  /// If the deque is full and needs to be extended, returns `false`, the
  /// deque is not modified in that case.
  ///
  /// # Examples
  ///
  /// ```
  /// use std::collections::VecDeque;
  ///
  /// let mut buf = VecDeque::new();
  /// buf.push_back(5);
  /// buf.push_back(10);
  /// buf.push_back(15);
  /// assert_eq!(buf, [5, 10, 15]);
  ///
  /// buf.resize_with(5, Default::default);
  /// assert_eq!(buf, [5, 10, 15, 0, 0]);
  ///
  /// buf.resize_with(2, || unreachable!());
  /// assert_eq!(buf, [5, 10]);
  ///
  /// let mut state = 100;
  /// buf.resize_with(5, || { state += 1; state });
  /// assert_eq!(buf, [5, 10, 101, 102, 103]);
  /// ```
  pub fn resize_with(&mut self, new_len: usize, generator: impl FnMut() -> T) -> bool {
    let len = self.len;
    if new_len > self.capacity() {
      return false;
    }

    if new_len > len {
      for val in repeat_with(generator).take(new_len - len) {
        self.push_back(val);
      }
    } else {
      self.truncate(new_len);
    }
    true
  }
}

impl<T, N> Drop for GenericArrayVecDeque<T, N>
where
  N: ArrayLength,
{
  fn drop(&mut self) {
    self.clear();
  }
}

impl<T, N> GenericArrayVecDeque<T, N>
where
  N: ArrayLength,
{
  /// Marginally more convenient
  #[inline]
  const fn ptr(&self) -> *const MaybeUninit<T> {
    self.array.as_slice().as_ptr()
  }

  /// Marginally more convenient
  #[inline]
  const fn ptr_mut(&mut self) -> *mut MaybeUninit<T> {
    self.array.as_mut_slice().as_mut_ptr()
  }

  /// Given a range into the logical buffer of the deque, this function
  /// return two ranges into the physical buffer that correspond to
  /// the given range. The `len` parameter should usually just be `self.len`;
  /// the reason it's passed explicitly is that if the deque is wrapped in
  /// a `Drain`, then `self.len` is not actually the length of the deque.
  ///
  /// # Safety
  ///
  /// This function is always safe to call. For the resulting ranges to be valid
  /// ranges into the physical buffer, the caller must ensure that the result of
  /// calling `slice::range(range, ..len)` represents a valid range into the
  /// logical buffer, and that all elements in that range are initialized.
  const fn slice_full_ranges(&self) -> (Range<usize>, Range<usize>) {
    let start = 0;
    let end = self.len;
    let len = end - start;

    if len == 0 {
      (0..0, 0..0)
    } else {
      // `slice::range` guarantees that `start <= end <= len`.
      // because `len != 0`, we know that `start < end`, so `start < len`
      // and the indexing is valid.
      let wrapped_start = self.to_physical_idx(start);

      // this subtraction can never overflow because `wrapped_start` is
      // at most `self.capacity()` (and if `self.capacity != 0`, then `wrapped_start` is strictly less
      // than `self.capacity`).
      let head_len = self.capacity() - wrapped_start;

      if head_len >= len {
        // we know that `len + wrapped_start <= self.capacity <= usize::MAX`, so this addition can't overflow
        (wrapped_start..wrapped_start + len, 0..0)
      } else {
        // can't overflow because of the if condition
        let tail_len = len - head_len;
        (wrapped_start..self.capacity(), 0..tail_len)
      }
    }
  }

  /// Returns the index in the underlying buffer for a given logical element
  /// index + addend.
  #[inline]
  const fn wrap_add(&self, idx: usize, addend: usize) -> usize {
    wrap_index(idx.wrapping_add(addend), self.capacity())
  }

  #[inline]
  const fn to_physical_idx(&self, idx: usize) -> usize {
    self.wrap_add(self.head, idx)
  }

  /// Returns the index in the underlying buffer for a given logical element
  /// index - subtrahend.
  #[inline]
  const fn wrap_sub(&self, idx: usize, subtrahend: usize) -> usize {
    wrap_index(
      idx.wrapping_sub(subtrahend).wrapping_add(self.capacity()),
      self.capacity(),
    )
  }

  /// Moves an element out of the buffer
  ///
  /// ## Safety
  /// - `off` must be a valid index into the buffer containing an initialized value
  #[inline]
  const unsafe fn buffer_read(&self, off: usize) -> T {
    unsafe { (&*self.ptr().add(off)).assume_init_read() }
  }

  /// Returns a slice pointer into the buffer.
  /// `range` must lie inside `0..self.capacity()`.
  #[inline]
  const unsafe fn buffer_range(&self, range: Range<usize>) -> *const [T] {
    unsafe { ptr::slice_from_raw_parts(self.ptr().add(range.start) as _, range.end - range.start) }
  }

  /// Returns a slice pointer into the buffer.
  /// `range` must lie inside `0..self.capacity()`.
  #[inline]
  const unsafe fn buffer_range_mut(&mut self, range: Range<usize>) -> *mut [T] {
    unsafe {
      ptr::slice_from_raw_parts_mut(
        self.ptr_mut().add(range.start) as _,
        range.end - range.start,
      )
    }
  }

  /// Writes an element into the buffer, moving it and returning a pointer to it.
  /// # Safety
  ///
  /// May only be called if `off < self.capacity()`.
  #[inline]
  const unsafe fn buffer_write(&mut self, off: usize, value: T) -> &mut T {
    unsafe {
      let ptr = &mut *self.ptr_mut().add(off);
      ptr.write(value);
      ptr.assume_init_mut()
    }
  }

  const unsafe fn rotate_left_inner(&mut self, mid: usize) {
    debug_assert!(mid * 2 <= self.len());
    unsafe {
      self.wrap_copy(self.head, self.to_physical_idx(self.len), mid);
    }
    self.head = self.to_physical_idx(mid);
  }

  const unsafe fn rotate_right_inner(&mut self, k: usize) {
    debug_assert!(k * 2 <= self.len());
    self.head = self.wrap_sub(self.head, k);
    unsafe {
      self.wrap_copy(self.to_physical_idx(self.len), self.head, k);
    }
  }

  /// Copies a contiguous block of memory len long from src to dst
  #[inline]
  const unsafe fn copy(&mut self, src: usize, dst: usize, len: usize) {
    debug_assert!(
      dst + len <= self.capacity(),
      // "cpy dst={} src={} len={} cap={}",
      // dst,
      // src,
      // len,
      // self.capacity()
    );
    debug_assert!(
      src + len <= self.capacity(),
      // "cpy dst={} src={} len={} cap={}",
      // dst,
      // src,
      // len,
      // self.capacity()
    );
    unsafe {
      ptr::copy(self.ptr().add(src), self.ptr().add(dst) as _, len);
    }
  }

  /// Copies a contiguous block of memory len long from src to dst
  #[inline]
  const unsafe fn copy_nonoverlapping(&mut self, src: usize, dst: usize, len: usize) {
    debug_assert!(
      dst + len <= self.capacity(),
      // "cno dst={} src={} len={} cap={}",
      // dst,
      // src,
      // len,
      // self.capacity()
    );
    debug_assert!(
      src + len <= self.capacity(),
      // "cno dst={} src={} len={} cap={}",
      // dst,
      // src,
      // len,
      // self.capacity()
    );
    unsafe {
      ptr::copy_nonoverlapping(self.ptr().add(src), self.ptr().add(dst) as _, len);
    }
  }

  /// Copies a potentially wrapping block of memory len long from src to dest.
  /// (abs(dst - src) + len) must be no larger than capacity() (There must be at
  /// most one continuous overlapping region between src and dest).
  const unsafe fn wrap_copy(&mut self, src: usize, dst: usize, len: usize) {
    // debug_assert!(
    //   cmp::min(src.abs_diff(dst), self.capacity() - src.abs_diff(dst)) + len <= self.capacity(),
    //   "wrc dst={} src={} len={} cap={}",
    //   dst,
    //   src,
    //   len,
    //   self.capacity()
    // );

    // If T is a ZST, don't do any copying.
    if mem::size_of::<T>() == 0 || src == dst || len == 0 {
      return;
    }

    let dst_after_src = self.wrap_sub(dst, src) < len;

    let src_pre_wrap_len = self.capacity() - src;
    let dst_pre_wrap_len = self.capacity() - dst;
    let src_wraps = src_pre_wrap_len < len;
    let dst_wraps = dst_pre_wrap_len < len;

    match (dst_after_src, src_wraps, dst_wraps) {
      (_, false, false) => {
        // src doesn't wrap, dst doesn't wrap
        //
        //        S . . .
        // 1 [_ _ A A B B C C _]
        // 2 [_ _ A A A A B B _]
        //            D . . .
        //
        unsafe {
          self.copy(src, dst, len);
        }
      }
      (false, false, true) => {
        // dst before src, src doesn't wrap, dst wraps
        //
        //    S . . .
        // 1 [A A B B _ _ _ C C]
        // 2 [A A B B _ _ _ A A]
        // 3 [B B B B _ _ _ A A]
        //    . .           D .
        //
        unsafe {
          self.copy(src, dst, dst_pre_wrap_len);
          self.copy(src + dst_pre_wrap_len, 0, len - dst_pre_wrap_len);
        }
      }
      (true, false, true) => {
        // src before dst, src doesn't wrap, dst wraps
        //
        //              S . . .
        // 1 [C C _ _ _ A A B B]
        // 2 [B B _ _ _ A A B B]
        // 3 [B B _ _ _ A A A A]
        //    . .           D .
        //
        unsafe {
          self.copy(src + dst_pre_wrap_len, 0, len - dst_pre_wrap_len);
          self.copy(src, dst, dst_pre_wrap_len);
        }
      }
      (false, true, false) => {
        // dst before src, src wraps, dst doesn't wrap
        //
        //    . .           S .
        // 1 [C C _ _ _ A A B B]
        // 2 [C C _ _ _ B B B B]
        // 3 [C C _ _ _ B B C C]
        //              D . . .
        //
        unsafe {
          self.copy(src, dst, src_pre_wrap_len);
          self.copy(0, dst + src_pre_wrap_len, len - src_pre_wrap_len);
        }
      }
      (true, true, false) => {
        // src before dst, src wraps, dst doesn't wrap
        //
        //    . .           S .
        // 1 [A A B B _ _ _ C C]
        // 2 [A A A A _ _ _ C C]
        // 3 [C C A A _ _ _ C C]
        //    D . . .
        //
        unsafe {
          self.copy(0, dst + src_pre_wrap_len, len - src_pre_wrap_len);
          self.copy(src, dst, src_pre_wrap_len);
        }
      }
      (false, true, true) => {
        // dst before src, src wraps, dst wraps
        //
        //    . . .         S .
        // 1 [A B C D _ E F G H]
        // 2 [A B C D _ E G H H]
        // 3 [A B C D _ E G H A]
        // 4 [B C C D _ E G H A]
        //    . .         D . .
        //
        debug_assert!(dst_pre_wrap_len > src_pre_wrap_len);
        let delta = dst_pre_wrap_len - src_pre_wrap_len;
        unsafe {
          self.copy(src, dst, src_pre_wrap_len);
          self.copy(0, dst + src_pre_wrap_len, delta);
          self.copy(delta, 0, len - dst_pre_wrap_len);
        }
      }
      (true, true, true) => {
        // src before dst, src wraps, dst wraps
        //
        //    . .         S . .
        // 1 [A B C D _ E F G H]
        // 2 [A A B D _ E F G H]
        // 3 [H A B D _ E F G H]
        // 4 [H A B D _ E F F G]
        //    . . .         D .
        //
        debug_assert!(src_pre_wrap_len > dst_pre_wrap_len);
        let delta = src_pre_wrap_len - dst_pre_wrap_len;
        unsafe {
          self.copy(0, delta, len - src_pre_wrap_len);
          self.copy(self.capacity() - delta, 0, delta);
          self.copy(src, dst, dst_pre_wrap_len);
        }
      }
    }
  }

  #[inline]
  const fn is_contiguous(&self) -> bool {
    // Do the calculation like this to avoid overflowing if len + head > usize::MAX
    self.head <= self.capacity() - self.len
  }
}

/// Returns the index in the underlying buffer for a given logical element index.
#[inline]
const fn wrap_index(logical_index: usize, capacity: usize) -> usize {
  debug_assert!(
    (logical_index == 0 && capacity == 0)
      || logical_index < capacity
      || (logical_index - capacity) < capacity
  );
  if logical_index >= capacity {
    logical_index - capacity
  } else {
    logical_index
  }
}
