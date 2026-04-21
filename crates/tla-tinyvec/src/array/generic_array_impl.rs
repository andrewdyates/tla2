// Copyright 2026 Dropbox, Inc.
// Author: Andrew Yates <ayates@dropbox.com>
// Licensed under the Apache License, Version 2.0

use core::default;

use super::Array;
use generic_array::{ArrayLength, GenericArray};

impl<T: Default, N: ArrayLength> Array for GenericArray<T, N> {
  type Item = T;
  const CAPACITY: usize = N::USIZE;

  #[inline(always)]
  fn as_slice(&self) -> &[T] {
    &*self
  }

  #[inline(always)]
  fn as_slice_mut(&mut self) -> &mut [T] {
    &mut *self
  }

  #[inline(always)]
  fn default() -> Self {
    <Self as Default>::default()
  }
}
