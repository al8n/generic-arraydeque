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
    buf
      .try_reserve(len)
      .map_err(|_| io::ErrorKind::OutOfMemory)?;

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
    buf
      .try_reserve(len)
      .map_err(|_| io::ErrorKind::OutOfMemory)?;

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
  #[allow(unstable_name_collisions)]
  fn split_at_checked(&self, mid: usize) -> Option<(&Self, &Self)>;
}

trait SplitAtMut {
  #[allow(unstable_name_collisions)]
  fn split_at_mut_checked(&mut self, mid: usize) -> Option<(&mut Self, &mut Self)>;
}

#[rustversion::since(1.80)]
impl<T> SplitAt for [T] {
  #[allow(unstable_name_collisions)]
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn split_at_checked(&self, mid: usize) -> Option<(&Self, &Self)> {
    <[T]>::split_at_checked(self, mid)
  }
}

#[rustversion::before(1.80)]
impl<T> SplitAt for [T] {
  #[allow(unstable_name_collisions)]
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn split_at_checked(&self, mid: usize) -> Option<(&Self, &Self)> {
    use core::slice::from_raw_parts;

    let len = self.len();
    if mid <= len {
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
  #[allow(unstable_name_collisions)]
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn split_at_mut_checked(&mut self, mid: usize) -> Option<(&mut Self, &mut Self)> {
    <[T]>::split_at_mut_checked(self, mid)
  }
}

#[rustversion::before(1.80)]
impl<T> SplitAtMut for [T] {
  #[allow(unstable_name_collisions)]
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn split_at_mut_checked(&mut self, mid: usize) -> Option<(&mut Self, &mut Self)> {
    use core::slice::from_raw_parts_mut;
    let len = self.len();
    if mid <= len {
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

#[cfg(test)]
mod tests {
  use crate::{typenum::{U2, U4, U6, U8}, GenericArrayDeque};
  use std::{
    io::{self, BufRead, IoSlice, Read, Write},
    string::String,
    vec::Vec,
  };

  #[test]
  fn read_consumes_front_slice() {
    let mut deque = GenericArrayDeque::<u8, U8>::new();
    for byte in b"hello" {
      assert!(deque.push_back(*byte).is_none());
    }

    let mut buf = [0u8; 3];
    let read = Read::read(&mut deque, &mut buf).unwrap();
    assert_eq!(read, 3);
    assert_eq!(&buf[..read], b"hel");
    assert_eq!(deque.into_iter().collect::<Vec<_>>(), b"lo".to_vec());
  }

  #[test]
  fn read_exact_handles_wrapped_storage() {
    let mut deque = GenericArrayDeque::<u8, U4>::new();
    for byte in b"abcd" {
      assert!(deque.push_back(*byte).is_none());
    }
    assert_eq!(deque.pop_front(), Some(b'a'));
    assert!(deque.push_back(b'e').is_none());

    let mut buf = [0u8; 3];
    deque.read_exact(&mut buf).unwrap();
    assert_eq!(&buf, b"bcd");
    assert_eq!(deque.into_iter().collect::<Vec<_>>(), vec![b'e']);
  }

  #[test]
  fn read_exact_reports_eof() {
    let mut deque = GenericArrayDeque::<u8, U4>::new();
    assert!(deque.push_back(b'x').is_none());

    let mut buf = [0u8; 2];
    let err = Read::read_exact(&mut deque, &mut buf).unwrap_err();
    assert_eq!(err.kind(), io::ErrorKind::UnexpectedEof);
  }

  #[test]
  fn read_to_end_and_string_clear_buffer() {
    let mut deque = GenericArrayDeque::<u8, U6>::new();
    for byte in b"abc" {
      assert!(deque.push_back(*byte).is_none());
    }
    let mut buf = Vec::new();
    deque.read_to_end(&mut buf).unwrap();
    assert_eq!(buf, b"abc");
    assert!(deque.is_empty());

    for byte in b"de" {
      assert!(deque.push_back(*byte).is_none());
    }
    let mut string = String::new();
    deque.read_to_string(&mut string).unwrap();
    assert_eq!(string, "de");
    assert_eq!(deque.len(), 2);

    deque.clear();
    deque.push_back(0xFF);
    let mut invalid = String::new();
    let err = deque.read_to_string(&mut invalid).unwrap_err();
    assert_eq!(err.kind(), io::ErrorKind::InvalidData);
  }

  #[test]
  fn bufread_fill_and_consume() {
    let mut deque = GenericArrayDeque::<u8, U4>::new();
    for byte in b"abcd" {
      assert!(deque.push_back(*byte).is_none());
    }

    let buf = BufRead::fill_buf(&mut deque).unwrap();
    assert_eq!(buf, b"abcd");
    BufRead::consume(&mut deque, 3);
    assert_eq!(deque.into_iter().collect::<Vec<_>>(), vec![b'd']);
  }

  #[test]
  fn write_variants_respect_capacity() {
    let mut deque = GenericArrayDeque::<u8, U4>::new();
    let written = Write::write(&mut deque, b"abcdef").unwrap();
    assert_eq!(written, 6);
    assert_eq!(deque.len(), 4);

    let mut deque = GenericArrayDeque::<u8, U8>::new();
    let slices = [IoSlice::new(b"ab"), IoSlice::new(b"cd")];
    assert_eq!(Write::write_vectored(&mut deque, &slices).unwrap(), 4);
    assert_eq!(deque.len(), 4);
    let overflow = [IoSlice::new(b"1234"), IoSlice::new(b"5678")];
    let err = Write::write_vectored(&mut deque, &overflow).unwrap_err();
    assert_eq!(err.kind(), io::ErrorKind::WriteZero);

    let mut deque = GenericArrayDeque::<u8, U4>::new();
    Write::write_all(&mut deque, b"wxyz").unwrap();
    let err = Write::write_all(&mut deque, b"overflow").unwrap_err();
    assert_eq!(err.kind(), io::ErrorKind::WriteZero);

    let mut deque = GenericArrayDeque::<u8, U2>::new();
    Write::flush(&mut deque).unwrap();
  }
}
