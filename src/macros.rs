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

macro_rules! push_back_unchecked {
  ($this:ident($value:ident)) => {{
    let len = $this.len;
    $this.len += 1;
    let idx = $this.to_physical_idx(len);

    // SAFETY: idx is guaranteed to be in-bounds and uninitialized

    let ptr = &mut *$this.ptr_mut().add(idx);
    ptr.write($value);
    ptr
  }};
}

macro_rules! push_front_unchecked {
  ($this:ident($value:ident)) => {{
    $this.head = $this.wrap_sub($this.head, 1);
    $this.len += 1;
    // SAFETY: head is guaranteed to be in-bounds and uninitialized
    let ptr = &mut *$this.ptr_mut().add($this.head);
    ptr.write($value);
    ptr
  }};
}

pub(super) use insert;
pub(super) use push_back_unchecked;
pub(super) use push_front_unchecked;
