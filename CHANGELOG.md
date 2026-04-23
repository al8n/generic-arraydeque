# UNRELEASED

# 0.2.0 (Apr 23rd, 2026)

BUG FIXES

- Fix undefined behavior in `Clone` and `clone_from`: previously byte-copied
  the `MaybeUninit<T>` storage instead of cloning each element, causing a
  double-free on drop for non-`Copy` types such as `String`, `Vec`, `Box`,
  `Rc`, and `Arc`. Verified under Miri.
- Fix `Read::read_to_string` to validate UTF-8 across the ring buffer's split
  so that codepoints straddling the boundary are no longer rejected as
  `InvalidData`, and to drain the deque on success, matching the
  `Read::read_to_string` contract.
- Fix `Read::read_exact` to leave buffered data in place on `UnexpectedEof`
  instead of clearing the deque, matching `std::collections::VecDeque`.
- Fix `Write::write` to return the actual number of bytes written instead of
  `buf.len()` when the deque has less remaining capacity than the input.
- Fix `Write::write_vectored` to perform partial writes up to remaining
  capacity instead of returning `WriteZero`, matching scalar `Write::write`
  semantics.
- Fix `try_from_exact_iter` and `try_extend_from_exact_iter` to bound the
  fill loop by capacity so a misbehaving `ExactSizeIterator` that yields
  more items than its advertised length can no longer push `self.len` past
  capacity (which would later cause undefined behavior on drop/access).

# 0.1.0 (Nov 9th, 2025)

FEATURES

- Fully on stack `VecDeque` implementation
