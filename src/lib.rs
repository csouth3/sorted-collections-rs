// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! sorted-collections-rs is a library providing useful extension traits and convenience
//! methods for ordered collections in Rust.

#![feature(core)]

#![cfg_attr(test, feature(collections, test))]
#[cfg(test)] extern crate test;

pub use sortedmap::SortedMapExt;
pub use sortedset::SortedSetExt;

pub mod sortedmap;
pub mod sortedset;
