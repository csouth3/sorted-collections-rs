#![allow(staged_unstable, staged_experimental)]

#[cfg(test)] extern crate test;

pub use traits::SortedSet;

pub mod traits;
pub mod impls;
