use super::*;

pub use extract_if::ExtractIf;

mod extract_if;

impl<T, N: ArrayLength> GenericArrayDeque<T, N> {
  /// Removes and returns the first element from the deque if the predicate
  /// returns `true`, or [`None`] if the predicate returns false or the deque
  /// is empty (the predicate will not be called in that case).
  ///
  /// ## Examples
  ///
  /// ```
  /// use generic_arraydeque::{GenericArrayDeque, typenum::U8};
  ///
  /// let mut deque = GenericArrayDeque::<i32, U8>::new();
  /// for value in 0..5 {
  ///     assert!(deque.push_back(value).is_none());
  /// }
  /// let pred = |x: &mut i32| *x % 2 == 0;
  ///
  /// assert_eq!(deque.pop_front_if(pred), Some(0));
  /// assert_eq!(deque.front(), Some(&1));
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

  /// Removes and returns the last element from the deque if the predicate
  /// returns `true`, or [`None`] if the predicate returns false or the deque
  /// is empty (the predicate will not be called in that case).
  ///
  /// ## Examples
  ///
  /// ```
  /// use generic_arraydeque::{GenericArrayDeque, typenum::U8};
  ///
  /// let mut deque = GenericArrayDeque::<i32, U8>::new();
  /// for value in 0..5 {
  ///     assert!(deque.push_back(value).is_none());
  /// }
  /// let pred = |x: &mut i32| *x % 2 == 0;
  ///
  /// assert_eq!(deque.pop_back_if(pred), Some(4));
  /// assert_eq!(deque.back(), Some(&3));
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
  /// use generic_arraydeque::{GenericArrayDeque, typenum::U2};
  ///
  /// let mut deque: GenericArrayDeque<u32, U2> = GenericArrayDeque::new();
  /// let elem_ref = deque.push_back_mut(10).unwrap();
  /// *elem_ref += 5;
  /// assert_eq!(*deque.get(0).unwrap(), 15);
  /// let _ = deque.push_back_mut(20).unwrap();
  /// assert!(deque.push_back_mut(30).is_err());
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  #[rustversion::attr(since(1.85), const)]
  pub fn push_back_mut(&mut self, value: T) -> Result<&mut T, T> {
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

  /// Prepends an element to the front of the deque, returning a mutable reference to it if successful.
  ///
  /// If the deque is at full capacity, returns the element back without modifying the deque.
  ///
  /// ## Examples
  ///
  /// ```
  /// use generic_arraydeque::{GenericArrayDeque, typenum::U2};
  ///
  /// let mut deque: GenericArrayDeque<u32, U2> = GenericArrayDeque::new();
  /// let elem_ref = deque.push_front_mut(10).unwrap();
  /// *elem_ref += 5;
  /// assert_eq!(*deque.get(0).unwrap(), 15);
  /// let _ = deque.push_front_mut(20).unwrap();
  /// assert!(deque.push_front_mut(30).is_err());
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  #[rustversion::attr(since(1.85), const)]
  pub fn push_front_mut(&mut self, value: T) -> Result<&mut T, T> {
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

  /// Shortens the deque, keeping the last `len` elements and dropping
  /// the rest.
  ///
  /// If `len` is greater or equal to the deque's current length, this has
  /// no effect.
  ///
  /// ## Examples
  ///
  /// ```
  /// use generic_arraydeque::{GenericArrayDeque, typenum::U4};
  ///
  /// let mut buf = GenericArrayDeque::<u32, U4>::new();
  /// assert!(buf.push_front(5).is_none());
  /// assert!(buf.push_front(10).is_none());
  /// assert!(buf.push_front(15).is_none());
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
  /// ```ignore
  /// use generic_arraydeque::{GenericArrayDeque, typenum::U8};
  ///
  /// let mut deque = GenericArrayDeque::<i32, U8>::try_from_iter([1, 2, 3]).unwrap();
  /// let x = deque.insert_mut(1, 5);
  /// *x += 7;
  /// assert_eq!(deque.into_iter().collect::<Vec<_>>(), vec![1, 12, 2, 3]);
  /// ```
  #[must_use = "if you don't need a reference to the value, use `GenericArrayDeque::insert` instead"]
  #[rustversion::attr(since(1.85), const)]
  pub fn insert_mut(&mut self, index: usize, value: T) -> Result<&mut T, T> {
    if index > self.len() || self.is_full() {
      return Err(value);
    }

    Ok(insert!(self(index, value)))
  }
}

impl<T: Clone, N: ArrayLength> GenericArrayDeque<T, N> {
  /// Clones the elements at the range `src` and appends them to the end.
  ///
  /// # Panics
  ///
  /// Panics if the starting index is greater than the end index
  /// or if either index is greater than the length of the vector.
  ///
  /// # Examples
  ///
  /// ```
  /// use generic_arraydeque::{GenericArrayDeque, typenum::U20};
  ///
  /// let mut characters = GenericArrayDeque::<_, U20>::try_from_exact_iter(['a', 'b', 'c', 'd', 'e']).unwrap();
  /// characters.extend_from_within(2..);
  /// assert_eq!(characters, ['a', 'b', 'c', 'd', 'e', 'c', 'd', 'e']);
  ///
  /// let mut numbers = GenericArrayDeque::<_, U20>::try_from_exact_iter([0, 1, 2, 3, 4]).unwrap();
  /// numbers.extend_from_within(..2);
  /// assert_eq!(numbers, [0, 1, 2, 3, 4, 0, 1]);
  ///
  /// let mut strings = GenericArrayDeque::<_, U20>::try_from_exact_iter([String::from("hello"), String::from("world"), String::from("!")]).unwrap();
  /// strings.extend_from_within(1..=2);
  /// assert_eq!(strings, ["hello", "world", "!", "world", "!"]);
  /// ```
  pub fn extend_from_within<R>(&mut self, src: R) -> bool
  where
    R: RangeBounds<usize>,
  {
    let Some(range) = try_range(src, ..self.len()) else {
      return false;
    };
    if range.len() > self.remaining_capacity() {
      return false;
    }

    // SAFETY:
    // - `slice::range` guarantees that the given range is valid for indexing self
    // - at least `range.len()` additional space is available
    unsafe {
      self.spec_extend_from_within(range);
    }
    true
  }

  /// Clones the elements at the range `src` and prepends them to the front.
  ///
  /// # Panics
  ///
  /// Panics if the starting index is greater than the end index
  /// or if either index is greater than the length of the vector.
  ///
  /// # Examples
  ///
  /// ```
  /// use generic_arraydeque::{GenericArrayDeque, typenum::U20};
  ///
  /// let mut characters = GenericArrayDeque::<_, U20>::try_from_exact_iter(['a', 'b', 'c', 'd', 'e']).unwrap();
  /// characters.prepend_from_within(2..);
  /// assert_eq!(characters, ['c', 'd', 'e', 'a', 'b', 'c', 'd', 'e']);
  ///
  /// let mut numbers = GenericArrayDeque::<_, U20>::try_from_exact_iter([0, 1, 2, 3, 4]).unwrap();
  /// numbers.prepend_from_within(..2);
  /// assert_eq!(numbers, [0, 1, 0, 1, 2, 3, 4]);
  ///
  /// let mut strings = GenericArrayDeque::<_, U20>::try_from_exact_iter([String::from("hello"), String::from("world"), String::from("!")]).unwrap();
  /// strings.prepend_from_within(1..=2);
  /// assert_eq!(strings, ["world", "!", "hello", "world", "!"]);
  /// ```
  pub fn prepend_from_within<R>(&mut self, src: R) -> bool
  where
    R: RangeBounds<usize>,
  {
    let Some(range) = try_range(src, ..self.len()) else {
      return false;
    };

    if range.len() > self.remaining_capacity() {
      return false;
    }

    // SAFETY:
    // - `slice::range` guarantees that the given range is valid for indexing self
    // - at least `range.len()` additional space is available
    unsafe {
      self.spec_prepend_from_within(range);
    }
    true
  }

  /// Get source, destination and count (like the arguments to [`ptr::copy_nonoverlapping`])
  /// for copying `count` values from index `src` to index `dst`.
  /// One of the ranges can wrap around the physical buffer, for this reason 2 triples are returned.
  ///
  /// Use of the word "ranges" specifically refers to `src..src + count` and `dst..dst + count`.
  ///
  /// # Safety
  ///
  /// - Ranges must not overlap: `src.abs_diff(dst) >= count`.
  /// - Ranges must be in bounds of the logical buffer: `src + count <= self.capacity()` and `dst + count <= self.capacity()`.
  /// - `head` must be in bounds: `head < self.capacity()`.
  unsafe fn nonoverlapping_ranges(
    &mut self,
    src: usize,
    dst: usize,
    count: usize,
    head: usize,
  ) -> [(*const T, *mut T, usize); 2] {
    // "`src` and `dst` must be at least as far apart as `count`"
    debug_assert!(
      src.abs_diff(dst) >= count,
      "`src` and `dst` must not overlap. src={src} dst={dst} count={count}",
    );
    debug_assert!(
      src.max(dst) + count <= self.capacity(),
      "ranges must be in bounds. src={src} dst={dst} count={count} cap={}",
      self.capacity(),
    );

    let wrapped_src = self.wrap_add(head, src);
    let wrapped_dst = self.wrap_add(head, dst);

    let room_after_src = self.capacity() - wrapped_src;
    let room_after_dst = self.capacity() - wrapped_dst;

    let src_wraps = room_after_src < count;
    let dst_wraps = room_after_dst < count;

    // Wrapping occurs if `capacity` is contained within `wrapped_src..wrapped_src + count` or `wrapped_dst..wrapped_dst + count`.
    // Since these two ranges must not overlap as per the safety invariants of this function, only one range can wrap.
    debug_assert!(
      !(src_wraps && dst_wraps),
      "BUG: at most one of src and dst can wrap. src={src} dst={dst} count={count} cap={}",
      self.capacity(),
    );

    unsafe {
      let ptr = self.ptr_mut() as *mut T;
      let src_ptr = ptr.add(wrapped_src) as _;
      let dst_ptr = ptr.add(wrapped_dst) as _;

      if src_wraps {
        [
          (src_ptr, dst_ptr, room_after_src),
          (ptr, dst_ptr.add(room_after_src), count - room_after_src),
        ]
      } else if dst_wraps {
        [
          (src_ptr, dst_ptr, room_after_dst),
          (src_ptr.add(room_after_dst), ptr, count - room_after_dst),
        ]
      } else {
        [
          (src_ptr, dst_ptr, count),
          // null pointers are fine as long as the count is 0
          (ptr::null(), ptr::null_mut(), 0),
        ]
      }
    }
  }

  unsafe fn spec_extend_from_within(&mut self, src: Range<usize>) {
    let dst = self.len();
    let count = src.end - src.start;
    let src = src.start;

    unsafe {
      // SAFETY:
      // - Ranges do not overlap: src entirely spans initialized values, dst entirely spans uninitialized values.
      // - Ranges are in bounds: guaranteed by the caller.
      let ranges = self.nonoverlapping_ranges(src, dst, count, self.head);

      // `len` is updated after every clone to prevent leaking and
      // leave the deque in the right state when a clone implementation panics

      for (src, dst, count) in ranges {
        for offset in 0..count {
          dst.add(offset).write((*src.add(offset)).clone());
          self.len += 1;
        }
      }
    }
  }

  unsafe fn spec_prepend_from_within(&mut self, src: Range<usize>) {
    let dst = 0;
    let count = src.end - src.start;
    let src = src.start + count;

    let new_head = self.wrap_sub(self.head, count);
    let cap = self.capacity();

    unsafe {
      // SAFETY:
      // - Ranges do not overlap: src entirely spans initialized values, dst entirely spans uninitialized values.
      // - Ranges are in bounds: guaranteed by the caller.
      let ranges = self.nonoverlapping_ranges(src, dst, count, new_head);

      // Cloning is done in reverse because we prepend to the front of the deque,
      // we can't get holes in the *logical* buffer.
      // `head` and `len` are updated after every clone to prevent leaking and
      // leave the deque in the right state when a clone implementation panics

      // Clone the first range
      let (src, dst, count) = ranges[1];
      for offset in (0..count).rev() {
        dst.add(offset).write((*src.add(offset)).clone());
        self.head -= 1;
        self.len += 1;
      }

      // Clone the second range
      let (src, dst, count) = ranges[0];
      let mut iter = (0..count).rev();
      if let Some(offset) = iter.next() {
        dst.add(offset).write((*src.add(offset)).clone());
        // After the first clone of the second range, wrap `head` around
        if self.head == 0 {
          self.head = cap;
        }
        self.head -= 1;
        self.len += 1;

        // Continue like normal
        for offset in iter {
          dst.add(offset).write((*src.add(offset)).clone());
          self.head -= 1;
          self.len += 1;
        }
      }
    }
  }
}
