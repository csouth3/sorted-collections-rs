// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! A trait extending ordered sets, along with associated impls and iterators.

use std::collections::Bound::{self, Excluded, Included, Unbounded};
use std::collections::btree_set::{self, BTreeSet};

/// An extension trait for a `Set` whose elements have a defined total ordering.
/// This trait defines convenience methods which take advantage of the set's ordering.
pub trait SortedSetExt<T>
    where T: Clone + Ord
{
    /// A by-value iterator yielding elements within a given range which have just been removed
    /// from this set.
    type RangeRemove;

    /// Returns an immutable reference to the first (least) element currently in this set.
    /// Returns `None` if this set is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// extern crate "sorted-collections" as sorted_collections;
    ///
    /// use std::collections::BTreeSet;
    /// use sorted_collections::SortedSetExt;
    ///
    /// fn main() {
    ///     let set: BTreeSet<u32> = vec![1u32, 2, 3, 4, 5].into_iter().collect();
    ///     assert_eq!(set.first().unwrap(), &1u32);
    /// }
    /// ```
    fn first(&self) -> Option<&T>;

    /// Removes and returns the first (least) element currently in this set.
    /// Returns `None` if this set is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// extern crate "sorted-collections" as sorted_collections;
    ///
    /// use std::collections::BTreeSet;
    /// use sorted_collections::SortedSetExt;
    ///
    /// fn main() {
    ///     let mut set: BTreeSet<u32> = vec![1u32, 2, 3, 4, 5].into_iter().collect();
    ///     assert_eq!(set.first_remove().unwrap(), 1u32);
    ///     assert_eq!(set.into_iter().collect::<Vec<u32>>(), vec![2u32, 3, 4, 5]);
    /// }
    /// ```
    fn first_remove(&mut self) -> Option<T>;

    /// Returns an immutable reference to the last (greatest) element currently in this set.
    /// Returns `None` if this set is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// extern crate "sorted-collections" as sorted_collections;
    ///
    /// use std::collections::BTreeSet;
    /// use sorted_collections::SortedSetExt;
    ///
    /// fn main() {
    ///     let set: BTreeSet<u32> = vec![1u32, 2, 3, 4, 5].into_iter().collect();
    ///     assert_eq!(set.last().unwrap(), &5u32);
    /// }
    /// ```
    fn last(&self) -> Option<&T>;

    /// Removes and returns the last (greatest) element currently in this set.
    /// Returns `None` if this set is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// extern crate "sorted-collections" as sorted_collections;
    ///
    /// use std::collections::BTreeSet;
    /// use sorted_collections::SortedSetExt;
    ///
    /// fn main() {
    ///     let mut set: BTreeSet<u32> = vec![1u32, 2, 3, 4, 5].into_iter().collect();
    ///     assert_eq!(set.last_remove().unwrap(), 5u32);
    ///     assert_eq!(set.into_iter().collect::<Vec<u32>>(), vec![1u32, 2, 3, 4]);
    /// }
    /// ```
    fn last_remove(&mut self) -> Option<T>;

    /// Returns an immutable reference to the least element in this set greater than or equal to `elem`.
    /// Returns `None` if there is no such element.
    ///
    /// # Examples
    ///
    /// ```
    /// extern crate "sorted-collections" as sorted_collections;
    ///
    /// use std::collections::BTreeSet;
    /// use sorted_collections::SortedSetExt;
    ///
    /// fn main() {
    ///     let set: BTreeSet<u32> = vec![1u32, 2, 3, 4, 5].into_iter().collect();
    ///     assert_eq!(set.ceiling(&3).unwrap(), &3u32);
    /// }
    /// ```
    fn ceiling(&self, elem: &T) -> Option<&T>;

    /// Removes and returns the least element in this set greater than or equal to `elem`.
    /// Returns `None` if there is no such element.
    ///
    /// # Examples
    ///
    /// ```
    /// extern crate "sorted-collections" as sorted_collections;
    ///
    /// use std::collections::BTreeSet;
    /// use sorted_collections::SortedSetExt;
    ///
    /// fn main() {
    ///     let mut set: BTreeSet<u32> = vec![1u32, 2, 3, 4, 5].into_iter().collect();
    ///     assert_eq!(set.ceiling_remove(&3).unwrap(), 3u32);
    ///     assert_eq!(set.into_iter().collect::<Vec<u32>>(), vec![1u32, 2, 4, 5]);
    /// }
    /// ```
    fn ceiling_remove(&mut self, elem: &T) -> Option<T>;

    /// Returns an immutable reference to the greatest element in this set less than or equal to `elem`.
    /// Returns `None` if there is no such element.
    ///
    /// # Examples
    ///
    /// ```
    /// extern crate "sorted-collections" as sorted_collections;
    ///
    /// use std::collections::BTreeSet;
    /// use sorted_collections::SortedSetExt;
    ///
    /// fn main() {
    ///     let set: BTreeSet<u32> = vec![1u32, 2, 3, 4, 5].into_iter().collect();
    ///     assert_eq!(set.floor(&3).unwrap(), &3u32);
    /// }
    /// ```
    fn floor(&self, elem: &T) -> Option<&T>;

    /// Removes and returns the greatest element in this set less than or equal to `elem`.
    /// Returns `None` if there is no such element.
    ///
    /// # Examples
    ///
    /// ```
    /// extern crate "sorted-collections" as sorted_collections;
    ///
    /// use std::collections::BTreeSet;
    /// use sorted_collections::SortedSetExt;
    ///
    /// fn main() {
    ///     let mut set: BTreeSet<u32> = vec![1u32, 2, 3, 4, 5].into_iter().collect();
    ///     assert_eq!(set.floor_remove(&3).unwrap(), 3u32);
    ///     assert_eq!(set.into_iter().collect::<Vec<u32>>(), vec![1u32, 2, 4, 5]);
    /// }
    /// ```
    fn floor_remove(&mut self, elem: &T) -> Option<T>;

    /// Returns an immutable reference to the least element in this set strictly greater than `elem`.
    /// Returns `None` if there is no such element.
    ///
    /// # Examples
    ///
    /// ```
    /// extern crate "sorted-collections" as sorted_collections;
    ///
    /// use std::collections::BTreeSet;
    /// use sorted_collections::SortedSetExt;
    ///
    /// fn main() {
    ///     let set: BTreeSet<u32> = vec![1u32, 2, 3, 4, 5].into_iter().collect();
    ///     assert_eq!(set.higher(&3).unwrap(), &4u32);
    /// }
    /// ```
    fn higher(&self, elem: &T) -> Option<&T>;

    /// Removes and returns the least element in this set strictly greater than `elem`.
    /// Returns `None` if there is no such element.
    ///
    /// # Examples
    ///
    /// ```
    /// extern crate "sorted-collections" as sorted_collections;
    ///
    /// use std::collections::BTreeSet;
    /// use sorted_collections::SortedSetExt;
    ///
    /// fn main() {
    ///     let mut set: BTreeSet<u32> = vec![1u32, 2, 3, 4, 5].into_iter().collect();
    ///     assert_eq!(set.higher_remove(&3).unwrap(), 4u32);
    ///     assert_eq!(set.into_iter().collect::<Vec<u32>>(), vec![1u32, 2, 3, 5]);
    /// }
    /// ```
    fn higher_remove(&mut self, elem: &T) -> Option<T>;

    /// Returns an immutable reference to the greatest element in this set strictly less than `elem`.
    /// Returns `None` if there is no such element.
    ///
    /// # Examples
    ///
    /// ```
    /// extern crate "sorted-collections" as sorted_collections;
    ///
    /// use std::collections::BTreeSet;
    /// use sorted_collections::SortedSetExt;
    ///
    /// fn main() {
    ///     let set: BTreeSet<u32> = vec![1u32, 2, 3, 4, 5].into_iter().collect();
    ///     assert_eq!(set.lower(&3).unwrap(), &2u32);
    /// }
    /// ```
    fn lower(&self, elem: &T) -> Option<&T>;

    /// Removes and returns the greatest element in this set strictly less than `elem`.
    /// Returns `None` if there is no such element.
    ///
    /// # Examples
    ///
    /// ```
    /// extern crate "sorted-collections" as sorted_collections;
    ///
    /// use std::collections::BTreeSet;
    /// use sorted_collections::SortedSetExt;
    ///
    /// fn main() {
    ///     let mut set: BTreeSet<u32> = vec![1u32, 2, 3, 4, 5].into_iter().collect();
    ///     assert_eq!(set.lower_remove(&3).unwrap(), 2u32);
    ///     assert_eq!(set.into_iter().collect::<Vec<u32>>(), vec![1u32, 3, 4, 5]);
    /// }
    /// ```
    fn lower_remove(&mut self, elem: &T) -> Option<T>;

    /// Removes the elements of this set in the range starting at `from_elem` and ending at
    /// `to_elem`, and returns a double-ended by-value iterator yielding the removed elements.
    ///
    /// If `from_elem` is `Unbounded`, then it will be treated as "negative infinity", and
    /// if `to_elem` is `Unbounded`, then it will be treated as "positive infinity".  Thus,
    /// `range_remove(Unbounded, Unbounded)` will clear the set and return a by-value
    /// iterator over all of the elements which were in it.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// extern crate "sorted-collections" as sorted_collections;
    ///
    /// use std::collections::Bound::{Excluded, Included};
    /// use std::collections::BTreeSet;
    /// use sorted_collections::SortedSetExt;
    ///
    /// fn main() {
    ///     let mut set: BTreeSet<u32> = vec![1u32, 2, 3, 4, 5].into_iter().collect();
    ///     assert_eq!(set.range_remove(Included(&2), Excluded(&4)).collect::<Vec<u32>>(),
    ///         vec![2u32, 3]);
    ///     assert_eq!(set.into_iter().collect::<Vec<u32>>(), vec![1u32, 4, 5]);
    /// }
    /// ```
    fn range_remove(&mut self, Bound<&T>, to_elem: Bound<&T>) -> Self::RangeRemove;
}

// A generic reusable impl of SortedSetExt.
macro_rules! sortedset_impl {
    ($typ:ty, $rangeremove:ident, $rangeremoveret:ty) => (
        fn first(&self) -> Option<&T> {
            self.iter().min()
        }

        fn first_remove(&mut self) -> Option<T> {
            match self.first().cloned() {
                Some(first) => {
                    let sanity = self.remove(&first);
                    debug_assert!(sanity);
                    Some(first)
                },
                _ => {
                    None
                },
            }
        }

        fn last(&self) -> Option<&T> {
            self.iter().max()
        }

        fn last_remove(&mut self) -> Option<T> {
            match self.last().cloned() {
                Some(last) => {
                    let sanity = self.remove(&last);
                    debug_assert!(sanity);
                    Some(last)
                },
                _ => {
                    None
                },
            }
        }

        fn ceiling(&self, elem: &T) -> Option<&T> {
            self.range(Included(elem), Unbounded).min()
        }

        fn ceiling_remove(&mut self, elem: &T) -> Option<T> {
            match self.ceiling(elem).cloned() {
                Some(ceiling) => {
                    let sanity = self.remove(&ceiling);
                    debug_assert!(sanity);
                    Some(ceiling)
                },
                _ => {
                    None
                },
            }
        }

        fn floor(&self, elem: &T) -> Option<&T> {
            self.range(Unbounded, Included(elem)).max()
        }

        fn floor_remove(&mut self, elem: &T) -> Option<T> {
            match self.floor(elem).cloned() {
                Some(floor) => {
                    let sanity = self.remove(&floor);
                    debug_assert!(sanity);
                    Some(floor)
                },
                _ => {
                    None
                },
            }
        }

        fn higher(&self, elem: &T) -> Option<&T> {
            self.range(Excluded(elem), Unbounded).min()
        }

        fn higher_remove(&mut self, elem: &T) -> Option<T> {
            match self.higher(elem).cloned() {
                Some(higher) => {
                    let sanity = self.remove(&higher);
                    debug_assert!(sanity);
                    Some(higher)
                },
                _ => {
                    None
                },
            }
        }

        fn lower(&self, elem: &T) -> Option<&T> {
            self.range(Unbounded, Excluded(elem)).max()
        }

        fn lower_remove(&mut self, elem: &T) -> Option<T> {
            match self.lower(elem).cloned() {
                Some(lower) => {
                    let sanity = self.remove(&lower);
                    debug_assert!(sanity);
                    Some(lower)
                },
                _ => {
                 None
                },
            }
        }

        fn range_remove(&mut self, from_elem: Bound<&T>, to_elem: Bound<&T>) -> $rangeremoveret {
            let ret: $typ = self.range(from_elem, to_elem).cloned().collect();

            for elem in &ret {
                let sanity = self.remove(elem);
                debug_assert!(sanity);
            }
            $rangeremove(ret.into_iter())
        }
    );
}

// An impl of SortedSetExt for the standard library BTreeSet
impl<'a, T> SortedSetExt<T> for BTreeSet<T>
    where T: Clone + Ord
{
    type RangeRemove = BTreeSetRangeRemove<T>;

    sortedset_impl!(BTreeSet<T>, BTreeSetRangeRemove, BTreeSetRangeRemove<T>);
}

/// A double-ended by-value iterator for removing pairs from a BTreeSet.
pub struct BTreeSetRangeRemove<T>(btree_set::IntoIter<T>);

impl<T> Iterator for BTreeSetRangeRemove<T> {
    type Item = T;

    fn next(&mut self) -> Option<T> { self.0.next() }
    fn size_hint(&self) -> (usize, Option<usize>) { self.0.size_hint() }
}
impl<T> DoubleEndedIterator for BTreeSetRangeRemove<T> {
    fn next_back(&mut self) -> Option<T> { self.0.next_back() }
}
impl<T> ExactSizeIterator for BTreeSetRangeRemove<T> {
    fn len(&self) -> usize { self.0.len() }
}

#[cfg(test)]
mod tests {
    use std::collections::Bound::{Excluded, Included};
    use std::collections::BTreeSet;

    use super::SortedSetExt;

    #[test]
    fn test_first() {
        let set: BTreeSet<u32> = vec![1u32, 2, 3, 4, 5].into_iter().collect();
        assert_eq!(set.first().unwrap(), &1u32);
    }

    #[test]
    fn test_first_remove() {
        let mut set: BTreeSet<u32> = vec![1u32, 2, 3, 4, 5].into_iter().collect();
        assert_eq!(set.first_remove().unwrap(), 1u32);
        assert_eq!(set.into_iter().collect::<Vec<u32>>(), vec![2u32, 3, 4, 5]);
    }

    #[test]
    fn test_last() {
        let set: BTreeSet<u32> = vec![1u32, 2, 3, 4, 5].into_iter().collect();
        assert_eq!(set.last().unwrap(), &5u32);
    }

    #[test]
    fn test_last_remove() {
        let mut set: BTreeSet<u32> = vec![1u32, 2, 3, 4, 5].into_iter().collect();
        assert_eq!(set.last_remove().unwrap(), 5u32);
        assert_eq!(set.into_iter().collect::<Vec<u32>>(), vec![1u32, 2, 3, 4]);
    }

    #[test]
    fn test_ceiling() {
        let set: BTreeSet<u32> = vec![1u32, 2, 3, 4, 5].into_iter().collect();
        assert_eq!(set.ceiling(&3).unwrap(), &3u32);
        assert_eq!(set.into_iter().collect::<Vec<u32>>(), vec![1u32, 2, 3, 4, 5]);
    }

    #[test]
    fn test_ceiling_remove() {
        let mut set: BTreeSet<u32> = vec![1u32, 2, 3, 4, 5].into_iter().collect();
        assert_eq!(set.ceiling_remove(&3).unwrap(), 3u32);
        assert_eq!(set.into_iter().collect::<Vec<u32>>(), vec![1u32, 2, 4, 5]);
    }

    #[test]
    fn test_floor() {
        let set: BTreeSet<u32> = vec![1u32, 2, 3, 4, 5].into_iter().collect();
        assert_eq!(set.floor(&3).unwrap(), &3u32);
        assert_eq!(set.into_iter().collect::<Vec<u32>>(), vec![1u32, 2, 3, 4, 5]);
    }

    #[test]
    fn test_floor_remove() {
        let mut set: BTreeSet<u32> = vec![1u32, 2, 3, 4, 5].into_iter().collect();
        assert_eq!(set.floor_remove(&3).unwrap(), 3u32);
        assert_eq!(set.into_iter().collect::<Vec<u32>>(), vec![1u32, 2, 4, 5]);
    }

    #[test]
    fn test_higher() {
        let set: BTreeSet<u32> = vec![1u32, 2, 3, 4, 5].into_iter().collect();
        assert_eq!(set.higher(&3).unwrap(), &4u32);
        assert_eq!(set.into_iter().collect::<Vec<u32>>(), vec![1u32, 2, 3, 4, 5]);
    }

    #[test]
    fn test_higher_remove() {
        let mut set: BTreeSet<u32> = vec![1u32, 2, 3, 4, 5].into_iter().collect();
        assert_eq!(set.higher_remove(&3).unwrap(), 4u32);
        assert_eq!(set.into_iter().collect::<Vec<u32>>(), vec![1u32, 2, 3, 5]);
    }

    #[test]
    fn test_lower() {
        let set: BTreeSet<u32> = vec![1u32, 2, 3, 4, 5].into_iter().collect();
        assert_eq!(set.lower(&3).unwrap(), &2u32);
        assert_eq!(set.into_iter().collect::<Vec<u32>>(), vec![1u32, 2, 3, 4, 5]);
    }

    #[test]
    fn test_lower_remove() {
        let mut set: BTreeSet<u32> = vec![1u32, 2, 3, 4, 5].into_iter().collect();
        assert_eq!(set.lower_remove(&3).unwrap(), 2u32);
        assert_eq!(set.into_iter().collect::<Vec<u32>>(), vec![1u32, 3, 4, 5]);
    }

    #[test]
    fn test_range_remove() {
        let mut set: BTreeSet<u32> = vec![1u32, 2, 3, 4, 5].into_iter().collect();
        assert_eq!(set.range_remove(Included(&2), Excluded(&4)).collect::<Vec<u32>>(),
            vec![2u32, 3]);
        assert_eq!(set.into_iter().collect::<Vec<u32>>(), vec![1u32, 4, 5]);
    }
}
