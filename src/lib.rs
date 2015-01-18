//! sorted-collections-rs is a library providing useful extension traits and convenience
//! methods for ordered collections in Rust.

#![experimental]

#![allow(unstable)]

#[cfg(test)] extern crate test;

#[experimental] pub use sortedmap::SortedMap;
#[experimental] pub use sortedset::SortedSet;

#[experimental] pub mod sortedmap;
#[experimental] pub mod sortedset;
