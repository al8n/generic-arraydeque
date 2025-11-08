use core::str::{from_utf8, from_utf8_unchecked};
use std::io::{self, BufRead, IoSlice, Read, Write};

use super::{ArrayLength, GenericArrayDeque};

impl<N: ArrayLength> GenericArrayDeque<u8, N> {
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn extend_bytes(&mut self, buf: &[u8]) {
    let written = unsafe {
      self.write_iter_wrapping(
        self.to_physical_idx(self.len),
        buf.iter().copied(),
        buf.len(),
      )
    };

    debug_assert_eq!(
      buf.len(),
      written,
      "The number of items written to VecDeque doesn't match the TrustedLen size hint"
    );
  }
}

/// Read is implemented for `GenericArrayDeque<u8>` by consuming bytes from the front of the `GenericArrayDeque`.
impl<N: ArrayLength> Read for GenericArrayDeque<u8, N> {
  /// Fill `buf` with the contents of the "front" slice as returned by
  /// [`as_slices`][`GenericArrayDeque::as_slices`]. If the contained byte slices of the `GenericArrayDeque` are
  /// discontiguous, multiple calls to `read` will be needed to read the entire content.
  #[inline]
  fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
    let (ref mut front, _) = self.as_slices();
    let n = Read::read(front, buf)?;
    self.drain(..n);
    Ok(n)
  }

  #[inline]
  fn read_exact(&mut self, buf: &mut [u8]) -> io::Result<()> {
    let (front, back) = self.as_slices();

    // Use only the front buffer if it is big enough to fill `buf`, else use
    // the back buffer too.
    match SplitAtMut::split_at_mut_checked(buf, front.len()) {
      None => buf.copy_from_slice(&front[..buf.len()]),
      Some((buf_front, buf_back)) => match SplitAt::split_at_checked(back, buf_back.len()) {
        Some((back, _)) => {
          buf_front.copy_from_slice(front);
          buf_back.copy_from_slice(back);
        }
        None => {
          self.clear();
          return Err(io::Error::new(
            io::ErrorKind::UnexpectedEof,
            "failed to fill whole buffer",
          ));
        }
      },
    }

    self.drain(..buf.len());
    Ok(())
  }

  #[inline]
  fn read_to_end(&mut self, buf: &mut Vec<u8>) -> io::Result<usize> {
    // The total len is known upfront so we can reserve it in a single call.
    let len = self.len();
    buf.try_reserve(len)?;

    let (front, back) = self.as_slices();
    buf.extend_from_slice(front);
    buf.extend_from_slice(back);
    self.clear();
    Ok(len)
  }

  #[inline]
  fn read_to_string(&mut self, buf: &mut String) -> io::Result<usize> {
    let (front, back) = self.as_slices();
    if from_utf8(front).is_err() || from_utf8(back).is_err() {
      return Err(io::Error::new(
        io::ErrorKind::InvalidData,
        "stream did not contain valid UTF-8",
      ));
    }

    let len = self.len();
    buf.try_reserve(len)?;

    // SAFETY: We have already verified that the data is valid UTF-8
    unsafe {
      buf.push_str(from_utf8_unchecked(front));
      buf.push_str(from_utf8_unchecked(back));
    }
    Ok(len)
  }
}

/// BufRead is implemented for `GenericArrayDeque<u8>` by reading bytes from the front of the `GenericArrayDeque`.
impl<N: ArrayLength> BufRead for GenericArrayDeque<u8, N> {
  /// Returns the contents of the "front" slice as returned by
  /// [`as_slices`][`GenericArrayDeque::as_slices`]. If the contained byte slices of the `GenericArrayDeque` are
  /// discontiguous, multiple calls to `fill_buf` will be needed to read the entire content.
  #[inline]
  fn fill_buf(&mut self) -> io::Result<&[u8]> {
    let (front, _) = self.as_slices();
    Ok(front)
  }

  #[inline]
  fn consume(&mut self, amt: usize) {
    self.drain(..amt);
  }
}

/// Write is implemented for `GenericArrayDeque<u8>` by appending to the `GenericArrayDeque`, growing it as needed.
impl<N: ArrayLength> Write for GenericArrayDeque<u8, N> {
  #[inline]
  fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
    let remaining = self.remaining_capacity();
    if remaining == 0 || buf.is_empty() {
      return Ok(0);
    }

    self.extend_bytes(buf[..remaining.min(buf.len())].as_ref());
    Ok(buf.len())
  }

  #[inline]
  fn write_vectored(&mut self, bufs: &[IoSlice<'_>]) -> io::Result<usize> {
    let len = bufs.iter().map(|b| b.len()).sum();
    if len > self.remaining_capacity() {
      return Err(io::Error::new(
        io::ErrorKind::WriteZero,
        "not enough capacity to write buffer",
      ));
    }

    for buf in bufs {
      self.extend_bytes(buf);
    }
    Ok(len)
  }

  #[inline]
  fn write_all(&mut self, buf: &[u8]) -> io::Result<()> {
    if buf.len() > self.remaining_capacity() {
      return Err(io::Error::new(
        io::ErrorKind::WriteZero,
        "not enough capacity to write buffer",
      ));
    }
    self.extend_bytes(buf);
    Ok(())
  }

  #[inline]
  fn flush(&mut self) -> io::Result<()> {
    Ok(())
  }
}

trait SplitAt {
  fn split_at_checked(&self, mid: usize) -> Option<(&Self, &Self)>;
}

trait SplitAtMut {
  fn split_at_mut_checked(&mut self, mid: usize) -> Option<(&mut Self, &mut Self)>;
}

#[rustversion::since(1.79)]
impl<T> SplitAt for [T] {
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn split_at_checked(&self, mid: usize) -> Option<(&Self, &Self)> {
    <[T]>::split_at_checked(self, mid)
  }
}

#[rustversion::before(1.79)]
impl<T> SplitAt for [T] {
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn split_at_checked(&self, mid: usize) -> Option<(&Self, &Self)> {
    use core::slice::from_raw_parts;

    if mid <= self.len() {
      // SAFETY: `0 <= mid <= self.len()`
      Some(unsafe {
        (
          from_raw_parts(self.as_ptr(), mid),
          from_raw_parts(self.as_ptr().add(mid), len - mid),
        )
      })
    } else {
      None
    }
  }
}

#[rustversion::since(1.80)]
impl<T> SplitAtMut for [T] {
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn split_at_mut_checked(&mut self, mid: usize) -> Option<(&mut Self, &mut Self)> {
    <[T]>::split_at_mut_checked(self, mid)
  }
}

#[rustversion::before(1.80)]
impl<T> SplitAtMut for [T] {
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn split_at_mut_checked(&mut self, mid: usize) -> Option<(&mut Self, &mut Self)> {
    use core::slice::from_raw_parts_mut;
    if mid <= self.len() {
      let len = self.len();
      // SAFETY: `0 <= mid <= self.len()`, so the two slices do not overlap.
      Some(unsafe {
        (
          from_raw_parts_mut(self.as_mut_ptr(), mid),
          from_raw_parts_mut(self.as_mut_ptr().add(mid), len - mid),
        )
      })
    } else {
      None
    }
  }
}
