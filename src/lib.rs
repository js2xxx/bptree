#![no_std]
#![deny(future_incompatible)]
#![deny(rust_2018_idioms)]
#![deny(rust_2024_compatibility)]
#![allow(edition_2024_expr_fragment_specifier)]
#![feature(maybe_uninit_slice)]
#![feature(map_try_insert)]

pub mod map;
mod mem;

extern crate alloc;

pub use map::BpTreeMap;
